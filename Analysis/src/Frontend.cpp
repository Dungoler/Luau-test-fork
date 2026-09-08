// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details

#include "Luau/Frontend.h"

#include "Luau/BuiltinDefinitions.h"
#include "Luau/Common.h"
#include "Luau/Clone.h"
#include "Luau/Config.h"
#include "Luau/ConstraintGenerator.h"
#include "Luau/ConstraintSet.h"
#include "Luau/ConstraintSolver.h"
#include "Luau/ControlFlowGraph.h"
#include "Luau/DataFlowGraph.h"
#include "Luau/DenseHash.h"
#include "Luau/DumpCFG.h"
#include "Luau/DcrLogger.h"
#include "Luau/ExpectedTypeVisitor.h"
#include "Luau/FileResolver.h"
#include "Luau/NonStrictTypeChecker.h"
#include "Luau/NotNull.h"
#include "Luau/Parser.h"
#include "Luau/Scope.h"
#include "Luau/Subtyping.h"
#include "Luau/TimeTrace.h"
#include "Luau/Type.h"
#include "Luau/TypeArena.h"
#include "Luau/TypeCheckLimits.h"
#include "Luau/TypePack.h"
#include "Luau/TypeUtils.h"
#include "Luau/TypeChecker2.h"
#include "Luau/TypeInfer.h"
#include "Luau/TypeStateMap.h"
#include "Luau/VisitType.h"

#include <algorithm>
#include <chrono>
#include <condition_variable>
#include <exception>
#include <mutex>
#include <string>
#include <unordered_map>
#include <utility>

LUAU_FASTINT(LuauTypeInferIterationLimit)
LUAU_FASTINT(LuauTypeInferRecursionLimit)
LUAU_FASTINT(LuauTarjanChildLimit)

LUAU_FASTFLAGVARIABLE(LuauKnowsTheDataModel3)
LUAU_FASTFLAGVARIABLE(LuauFrontendSourceNodeErase)

LUAU_FASTFLAG(LuauSolverV2)

LUAU_FASTFLAGVARIABLE(DebugLuauLogSolverToJson)
LUAU_FASTFLAGVARIABLE(DebugLuauLogSolverToJsonFile)
LUAU_FASTFLAGVARIABLE(DebugLuauForbidInternalTypes)
LUAU_FASTFLAGVARIABLE(DebugLuauForceStrictMode)
LUAU_FASTFLAGVARIABLE(DebugLuauForceNonStrictMode)
LUAU_FASTFLAGVARIABLE(DebugLuauAlwaysShowConstraintSolvingIncomplete)

LUAU_FASTFLAG(LuauStrictVisitInstantiatedType)
LUAU_FASTFLAG(LuauExportValueSyntax)
LUAU_FASTFLAGVARIABLE(LuauExportValueTypecheck)
LUAU_FLAGVERSION(LuauExportValueTypecheck, 2)

LUAU_FASTFLAGVARIABLE(LuauCyclicRequireTypeInference)
LUAU_FLAGVERSION(LuauCyclicRequireTypeInference, 6)

LUAU_FASTFLAGVARIABLE(LuauCyclicRequireTopLevelAccessError)

LUAU_FASTFLAGVARIABLE(DebugLuauForceOldSolver)

LUAU_FASTFLAG(LuauCFG)
LUAU_FASTFLAG(DebugLuauLogCFG)
LUAU_FASTFLAG(DebugLuauDumpCFGJson)

namespace Luau
{

struct BuildQueueModuleInfo
{
    ModuleName name;
    ModuleName humanReadableName;

    std::shared_ptr<SourceNode> sourceNode;
    std::shared_ptr<SourceModule> sourceModule;

    Config config;
    ScopePtr environmentScope;

    std::vector<RequireCycle> requireCycles;

    ModulePtr module;
    Frontend::Stats stats;
};

struct BuildQueueItem
{
    FrontendOptions options;
    bool recordJsonLog = false;

    ModuleSCCPtr scc;

    std::vector<BuildQueueModuleInfo> modules;

    std::vector<size_t> reverseDeps;
    int dirtyDependencies = 0;
    bool processing = false;

    std::exception_ptr exception;
};

struct BuildQueueWorkState
{
    std::function<void(std::function<void()> task)> executeTask_DEPRECATED;

    std::function<void(std::vector<std::function<void()>> tasks)> executeTasks;

    std::vector<BuildQueueItem> buildQueueItems;

    std::mutex mtx;
    std::condition_variable cv;

    std::vector<size_t> readyQueueItems;

    size_t processing = 0;
    size_t remaining = 0;
};

std::optional<Mode> parseMode(const std::vector<HotComment>& hotcomments)
{
    for (const HotComment& hc : hotcomments)
    {
        if (!hc.header)
            continue;

        if (hc.content == "nocheck")
            return Mode::NoCheck;

        if (hc.content == "nonstrict")
            return Mode::Nonstrict;

        if (hc.content == "strict")
            return Mode::Strict;
    }

    return std::nullopt;
}

static void generateDocumentationSymbols(TypeId ty, const std::string& rootName)
{
    if (ty->persistent)
        return;

    asMutable(ty)->documentationSymbol = rootName;

    if (TableType* ttv = getMutable<TableType>(ty))
    {
        for (auto& [name, prop] : ttv->props)
        {
            std::string n;

            n.reserve(rootName.size() + 1 + name.size());

            n += rootName;
            n += ".";
            n += name;

            prop.documentationSymbol = std::move(n);
        }
    }
    else if (ExternType* etv = getMutable<ExternType>(ty))
    {
        for (auto& [name, prop] : etv->props)
        {
            std::string n;

            n.reserve(rootName.size() + 1 + name.size());

            n += rootName;
            n += ".";
            n += name;

            prop.documentationSymbol = std::move(n);
        }
    }
}

static ParseResult parseSourceForModule(std::string_view source, Luau::SourceModule& sourceModule, bool captureComments)
{
    ParseOptions options;

    options.allowDeclarationSyntax = true;

    options.captureComments = captureComments;

    Luau::ParseResult parseResult = Luau::Parser::parse(source.data(), source.size(), *sourceModule.names, *sourceModule.allocator, options);

    sourceModule.root = parseResult.root;

    sourceModule.mode = Mode::Definition;

    if (options.captureComments)
    {
        sourceModule.hotcomments = parseResult.hotcomments;

        sourceModule.commentLocations = parseResult.commentLocations;
    }

    return parseResult;
}

static void persistCheckedTypes(ModulePtr checkedModule, GlobalTypes& globals, ScopePtr targetScope, const std::string& packageName)
{
    CloneState cloneState{globals.builtinTypes};

    std::vector<TypeId> typesToPersist;

    typesToPersist.reserve(checkedModule->declaredGlobals.size() + checkedModule->exportedTypeBindings.size());

    for (const auto& [name, ty] : checkedModule->declaredGlobals)
    {
        TypeId globalTy = clone(ty, globals.globalTypes, cloneState);

        static constexpr const char infix[] = "/global/";

        constexpr int infixLength = sizeof(infix) - 1;

        std::string documentationSymbol;

        documentationSymbol.reserve(packageName.size() + infixLength + name.size());

        documentationSymbol += packageName;

        documentationSymbol += infix;

        documentationSymbol += name;

        generateDocumentationSymbols(globalTy, documentationSymbol);

        targetScope->bindings[globals.globalNames.names->getOrAdd(name.c_str())] = {globalTy, Location(), false, {}, documentationSymbol};

        typesToPersist.push_back(globalTy);
    }

    for (const auto& [name, ty] : checkedModule->exportedTypeBindings)
    {
        TypeFun globalTy = clone(ty, globals.globalTypes, cloneState);

        static constexpr const char infix[] = "/globaltype/";

        constexpr int infixLength = sizeof(infix) - 1;

        std::string documentationSymbol;

        documentationSymbol.reserve(packageName.size() + infixLength + name.size());

        documentationSymbol += packageName;

        documentationSymbol += infix;

        documentationSymbol += name;

        generateDocumentationSymbols(globalTy.type, documentationSymbol);

        targetScope->exportedTypeBindings[name] = globalTy;

        typesToPersist.push_back(globalTy.type);
    }

    for (TypeId ty : typesToPersist)
    {
        persist(ty);
    }
}

LoadDefinitionFileResult Frontend::loadDefinitionFile(
    GlobalTypes& globals,
    ScopePtr targetScope,
    std::string_view source,
    const std::string& packageName,
    bool captureComments,
    bool typeCheckForAutocomplete
)
{
    LUAU_TIMETRACE_SCOPE("loadDefinitionFile", "Frontend");

    Luau::SourceModule sourceModule;

    sourceModule.name = packageName;

    sourceModule.humanReadableName = packageName;

    Luau::ParseResult parseResult = parseSourceForModule(source, sourceModule, captureComments);

    if (parseResult.errors.size() > 0)
    {
        return LoadDefinitionFileResult{false, std::move(parseResult), std::move(sourceModule), nullptr};
    }

    Frontend::Stats dummyStats;

    ModulePtr checkedModule = check(sourceModule, Mode::Definition, {}, std::nullopt, false, false, dummyStats, {});

    if (checkedModule->errors.size() > 0)
    {
        return LoadDefinitionFileResult{false, std::move(parseResult), std::move(sourceModule), std::move(checkedModule)};
    }

    persistCheckedTypes(checkedModule, globals, std::move(targetScope), packageName);

    return LoadDefinitionFileResult{true, std::move(parseResult), std::move(sourceModule), std::move(checkedModule)};
}

namespace
{

ErrorVec accumulateErrors(
    const std::unordered_map<ModuleName, std::shared_ptr<SourceNode>>& sourceNodes,
    ModuleResolver& moduleResolver,
    const ModuleName& name
)
{
    DenseHashSet<ModuleName> seen{{}};

    std::vector<ModuleName> queue{name};

    ErrorVec result;

    while (!queue.empty())
    {
        ModuleName next = std::move(queue.back());

        queue.pop_back();

        if (seen.contains(next))
            continue;

        seen.insert(next);

        auto it = sourceNodes.find(next);

        if (it == sourceNodes.end())
            continue;

        const SourceNode& sourceNode = *it->second;

        queue.insert(queue.end(), sourceNode.requireSet.begin(), sourceNode.requireSet.end());

        // FIXME: If a module has a syntax error, we won't be able to re-report it here.
        // The solution is probably to move errors from Module to SourceNode
        auto modulePtr = moduleResolver.getModule(next);

        if (!modulePtr)
            continue;

        Module& module = *modulePtr;

        size_t prevSize = result.size();

        result.insert(result.end(), module.errors.rbegin(), module.errors.rend());

        std::stable_sort(
            result.begin() + prevSize,
            result.end(),
            [](const TypeError& e1, const TypeError& e2) -> bool
            {
                return e1.location.begin > e2.location.begin;
            }
        );
    }

    std::reverse(result.begin(), result.end());

    return result;
}

void filterLintOptions(LintOptions& lintOptions, const std::vector<HotComment>& hotcomments, Mode mode)
{
    uint64_t ignoreLints = LintWarning::parseMask(hotcomments);

    lintOptions.warningMask &= ~ignoreLints;

    if (mode != Mode::NoCheck)
    {
        lintOptions.disableWarning(Luau::LintWarning::Code_UnknownGlobal);
    }

    if (mode == Mode::Strict)
    {
        lintOptions.disableWarning(Luau::LintWarning::Code_ImplicitReturn);
    }
}

// Runtime cycle detection only.
// Type-only dependencies intentionally do not participate.
std::vector<RequireCycle> getRequireCycles(
    const FileResolver* resolver,
    const std::unordered_map<ModuleName, std::shared_ptr<SourceNode>>& sourceNodes,
    const SourceNode* start
)
{
    std::vector<RequireCycle> result;

    DenseHashSet<const SourceNode*> seen(nullptr);

    std::vector<const SourceNode*> stack;
    std::vector<const SourceNode*> path;

    for (const auto& [depName, depLocation] : start->requireLocations)
    {
        std::vector<ModuleName> cycle;

        auto dit = sourceNodes.find(depName);

        if (dit == sourceNodes.end())
            continue;

        stack.push_back(dit->second.get());

        while (!stack.empty())
        {
            const SourceNode* top = stack.back();

            stack.pop_back();

            if (top == nullptr)
            {
                LUAU_ASSERT(!path.empty());

                top = path.back();

                path.pop_back();

                if (top == start)
                {
                    for (const SourceNode* node : path)
                    {
                        cycle.push_back(node->name);
                    }

                    cycle.push_back(top->name);

                    break;
                }
            }
            else if (!seen.contains(top))
            {
                seen.insert(top);

                path.push_back(top);

                stack.push_back(nullptr);

                for (size_t i = top->requireLocations.size(); i > 0; --i)
                {
                    const ModuleName& reqName = top->requireLocations[i - 1].first;

                    auto rit = sourceNodes.find(reqName);

                    if (rit != sourceNodes.end())
                    {
                        stack.push_back(rit->second.get());
                    }
                }
            }
        }

        path.clear();
        stack.clear();

        if (!cycle.empty())
        {
            result.emplace_back(RequireCycle{depLocation, std::move(cycle)});

            seen.clear();
        }
    }

    return result;
}

double getTimestamp()
{
    using namespace std::chrono;

    return double(duration_cast<nanoseconds>(high_resolution_clock::now().time_since_epoch()).count()) / 1e9;
}

} // namespace

static TypeCheckLimits makeTypeCheckLimits(const FrontendOptions& options)
{
    TypeCheckLimits limits;

    if (options.moduleTimeLimitSec)
    {
        limits.finishTime = TimeTrace::getClock() + *options.moduleTimeLimitSec;
    }
    else
    {
        limits.finishTime = std::nullopt;
    }

    limits.cancellationToken = options.cancellationToken;

    return limits;
}

Frontend::Frontend(SolverMode mode, FileResolver* fileResolver, ConfigResolver* configResolver, FrontendOptions options)
    : useNewLuauSolver(mode)
    , builtinTypes(NotNull{&builtinTypes_})
    , fileResolver(fileResolver)
    , moduleResolver(this)
    , moduleResolverForAutocomplete(this)
    , globals(builtinTypes, getLuauSolverMode())
    , globalsForAutocomplete(builtinTypes, getLuauSolverMode())
    , configResolver(configResolver)
    , options(std::move(options))
    , sccs{nullptr}
{
}

Frontend::Frontend(FileResolver* fileResolver, ConfigResolver* configResolver, const FrontendOptions& options)
    : useNewLuauSolver(FFlag::LuauSolverV2 ? SolverMode::New : SolverMode::Old)
    , builtinTypes(NotNull{&builtinTypes_})
    , fileResolver(fileResolver)
    , moduleResolver(this)
    , moduleResolverForAutocomplete(this)
    , globals(builtinTypes, getLuauSolverMode())
    , globalsForAutocomplete(builtinTypes, getLuauSolverMode())
    , configResolver(configResolver)
    , options(options)
    , sccs{nullptr}
{
}

void Frontend::setLuauSolverMode(SolverMode mode)
{
    useNewLuauSolver.store(mode);
}

SolverMode Frontend::getLuauSolverMode() const
{
    return useNewLuauSolver.load();
}

void Frontend::parse(const ModuleName& name)
{
    LUAU_TIMETRACE_SCOPE("Frontend::parse", "Frontend");

    LUAU_TIMETRACE_ARGUMENT("name", name.c_str());

    if (getCheckResult(name, false, false))
    {
        return;
    }

    std::vector<ModuleName> buildQueue;

    parseGraph(buildQueue, name, {}, false);
}

void Frontend::parseModules(const std::vector<ModuleName>& names)
{
    LUAU_TIMETRACE_SCOPE("Frontend::parseModules", "Frontend");

    DenseHashSet<Luau::ModuleName> seen{{}};

    for (const ModuleName& name : names)
    {
        if (seen.contains(name))
            continue;

        if (auto it = sourceNodes.find(name); it != sourceNodes.end() && !it->second->hasDirtySourceModule())
        {
            seen.insert(name);
            continue;
        }

        std::vector<ModuleName> queue;

        parseGraph(
            queue,
            name,
            {},
            false,
            [&seen](const ModuleName& name)
            {
                return seen.contains(name);
            }
        );

        seen.insert(name);
    }
}

CheckResult Frontend::check(const ModuleName& name, std::optional<FrontendOptions> optionOverride)
{
    LUAU_TIMETRACE_SCOPE("Frontend::check", "Frontend");

    LUAU_TIMETRACE_ARGUMENT("name", name.c_str());

    FrontendOptions frontendOptions = optionOverride.value_or(options);

    if (getLuauSolverMode() == SolverMode::New)
    {
        frontendOptions.forAutocomplete = false;
    }

    if (std::optional<CheckResult> result = getCheckResult(name, true, frontendOptions.forAutocomplete))
    {
        return std::move(*result);
    }

    TypeCheckLimits typeCheckLimits = makeTypeCheckLimits(frontendOptions);

    std::vector<ModuleName> buildQueue;

    DenseHashSet<Luau::ModuleName> seen{{}};

    bool cycleDetected = parseGraph(buildQueue, name, typeCheckLimits, frontendOptions.forAutocomplete);

    if (FFlag::LuauCyclicRequireTypeInference)
    {
        computeSCCs(buildQueue);
    }

    std::vector<BuildQueueItem> buildQueueItems;

    addBuildQueueItems(buildQueueItems, buildQueue, cycleDetected, seen, frontendOptions);

    if (buildQueueItems.empty())
    {
        return {};
    }

    checkBuildQueueItems(buildQueueItems);

    std::optional<CheckResult> result = getCheckResult(name, true, frontendOptions.forAutocomplete);

    if (result)
        return std::move(*result);

    return {};
}

bool Frontend::allModuleDependenciesValid(const ModuleName& name, bool forAutocomplete) const
{
    auto it = sourceNodes.find(name);

    if (it == sourceNodes.end())
        return false;

    const SourceNode& sourceNode = *it->second;

    if (sourceNode.hasInvalidModuleDependency(forAutocomplete))
    {
        return false;
    }

    for (const ModuleName& dep : sourceNode.requireSet)
    {
        auto depIt = sourceNodes.find(dep);

        if (depIt == sourceNodes.end())
            return false;

        if (depIt->second->hasInvalidModuleDependency(forAutocomplete))
        {
            return false;
        }
    }

    return true;
}

bool Frontend::isDirty(const ModuleName& name, bool forAutocomplete) const
{
    auto it = sourceNodes.find(name);

    if (it == sourceNodes.end())
        return true;

    return it->second->hasDirtyModule(forAutocomplete);
}

void Frontend::markDirty(const ModuleName& name, std::vector<ModuleName>* markedDirty)
{
    auto it = sourceNodes.find(name);

    if (it == sourceNodes.end())
        return;

    SourceNode& sourceNode = *it->second;

    if (sourceNode.dirtyModule)
        return;

    sourceNode.dirtyModule = true;
    sourceNode.dirtyModuleForAutocomplete = true;
    sourceNode.invalidModuleDependency = true;
    sourceNode.invalidModuleDependencyForAutocomplete = true;

    if (markedDirty)
        markedDirty->push_back(name);

    traverseDependents(
        name,
        [markedDirty](SourceNode& node)
        {
            if (node.dirtyModule)
                return false;

            node.dirtyModule = true;
            node.dirtyModuleForAutocomplete = true;

            node.invalidModuleDependency = true;
            node.invalidModuleDependencyForAutocomplete = true;

            if (markedDirty)
                markedDirty->push_back(node.name);

            return true;
        }
    );
}

void Frontend::traverseDependents(const ModuleName& name, std::function<bool(SourceNode&)> processSubtree)
{
    auto it = sourceNodes.find(name);

    if (it == sourceNodes.end())
        return;

    std::vector<SourceNode*> stack;

    stack.push_back(it->second.get());

    DenseHashSet<SourceNode*> seen;

    while (!stack.empty())
    {
        SourceNode* node = stack.back();

        stack.pop_back();

        if (seen.contains(node))
            continue;

        seen.insert(node);

        if (!processSubtree(*node))
            continue;

        for (const ModuleName& dependent : node->dependents)
        {
            auto dependentIt = sourceNodes.find(dependent);

            if (dependentIt != sourceNodes.end())
            {
                stack.push_back(dependentIt->second.get());
            }
        }

        if (FFlag::LuauCyclicRequireTypeInference)
        {
            for (const ModuleName& dependent : node->typeDependents)
            {
                auto dependentIt = sourceNodes.find(dependent);

                if (dependentIt != sourceNodes.end())
                {
                    stack.push_back(dependentIt->second.get());
                }
            }
        }
    }
}

SourceModule* Frontend::getSourceModule(const ModuleName& name)
{
    auto it = sourceModules.find(name);

    if (it == sourceModules.end())
        return nullptr;

    return it->second.get();
}

const SourceModule* Frontend::getSourceModule(const ModuleName& name) const
{
    auto it = sourceModules.find(name);

    if (it == sourceModules.end())
        return nullptr;

    return it->second.get();
}

struct InternalTypeFinder : TypeOnceVisitor
{
    InternalTypeFinder()
        : TypeOnceVisitor("InternalTypeFinder", /* skipBoundTypes */ true)
    {
    }

    bool visit(TypeId, const ExternType&) override
    {
        return false;
    }

    bool visit(TypeId, const BlockedType&) override
    {
        LUAU_ASSERT(false);
        return false;
    }

    bool visit(TypeId, const FreeType&) override
    {
        LUAU_ASSERT(false);
        return false;
    }

    bool visit(TypeId, const PendingExpansionType&) override
    {
        LUAU_ASSERT(false);
        return false;
    }

    bool visit(TypePackId, const BlockedTypePack&) override
    {
        LUAU_ASSERT(false);
        return false;
    }

    bool visit(TypePackId, const FreeTypePack&) override
    {
        LUAU_ASSERT(false);
        return false;
    }

    bool visit(TypePackId, const TypeFunctionInstanceTypePack&) override
    {
        LUAU_ASSERT(false);
        return false;
    }
};

ModulePtr check(
    const SourceModule& sourceModule,
    Mode mode,
    const std::vector<RequireCycle>& requireCycles,
    NotNull<BuiltinTypes> builtinTypes,
    NotNull<InternalErrorReporter> iceHandler,
    NotNull<ModuleResolver> moduleResolver,
    NotNull<FileResolver> fileResolver,
    const ScopePtr& parentScope,
    const ScopePtr& typeFunctionScope,
    std::function<void(const ModuleName&, const ScopePtr&)> prepareModuleScope,
    FrontendOptions options,
    TypeCheckLimits limits,
    bool recordJsonLog,
    Frontend::Stats& stats,
    std::function<void(const ModuleName&, std::string)> writeJsonLog
)
{
    LUAU_TIMETRACE_SCOPE("Frontend::check", "Typechecking");
    LUAU_TIMETRACE_ARGUMENT("module", sourceModule.name.c_str());
    LUAU_TIMETRACE_ARGUMENT("name", sourceModule.humanReadableName.c_str());

    ModulePtr module = std::make_shared<Module>();
    module->checkedInNewSolver = true;
    module->name = sourceModule.name;
    module->humanReadableName = sourceModule.humanReadableName;
    module->mode = mode;
    module->internalTypes.owningModule = module.get();
    module->interfaceTypes.owningModule = module.get();
    module->internalTypes.collectSingletonStats = options.collectTypeAllocationStats;
    module->allocator = sourceModule.allocator;
    module->names = sourceModule.names;
    module->root = sourceModule.root;

    iceHandler->moduleName = sourceModule.name;

    std::unique_ptr<DcrLogger> logger;
    if (recordJsonLog)
    {
        logger = std::make_unique<DcrLogger>();

        std::optional<SourceCode> source = fileResolver->readSource(module->name);
        if (source)
            logger->captureSource(source->source);
    }

    DataFlowGraph dfg = DataFlowGraphBuilder::build(
        sourceModule.root,
        NotNull{&module->defArena},
        NotNull{&module->keyArena},
        iceHandler
    );

    UnifierSharedState unifierState{iceHandler};
    unifierState.counters.recursionLimit = FInt::LuauTypeInferRecursionLimit;
    unifierState.counters.iterationLimit =
        limits.unifierIterationLimit.value_or(FInt::LuauTypeInferIterationLimit);

    Normalizer normalizer{
        &module->internalTypes,
        builtinTypes,
        NotNull{&unifierState},
        SolverMode::New
    };

    TypeFunctionRuntime typeFunctionRuntime{
        iceHandler,
        NotNull{&limits}
    };

    typeFunctionRuntime.allowEvaluation = true;

    Subtyping subtyping{
        builtinTypes,
        NotNull{&module->internalTypes},
        NotNull{&normalizer},
        NotNull{&typeFunctionRuntime},
        iceHandler
    };

    ConstraintGenerator cg{
        module,
        NotNull{&normalizer},
        NotNull{&typeFunctionRuntime},
        moduleResolver,
        builtinTypes,
        iceHandler,
        parentScope,
        typeFunctionScope,
        std::move(prepareModuleScope),
        logger.get(),
        NotNull{&dfg},
        requireCycles,
        nullptr,
        nullptr
    };

    ConstraintSet constraintSet = cg.run(sourceModule.root);

    module->errors = std::move(constraintSet.errors);
    module->constraintGenerationDidNotComplete = cg.recursionLimitMet;

    ConstraintSolver cs{
        NotNull{&normalizer},
        NotNull{&typeFunctionRuntime},
        module,
        moduleResolver,
        requireCycles,
        logger.get(),
        NotNull{&dfg},
        limits,
        std::move(constraintSet),
        nullptr,
        NotNull{&subtyping}
    };

    if (options.randomizeConstraintResolutionSeed)
        cs.randomize(*options.randomizeConstraintResolutionSeed);

    try
    {
        cs.run();
    }
    catch (const TimeLimitError&)
    {
        module->timeout = true;
    }
    catch (const UserCancelError&)
    {
        module->cancelled = true;
    }

    stats.dynamicConstraintsCreated += cs.solverConstraints.size();

    if (recordJsonLog)
    {
        std::string output = logger->compileOutput();

        if (FFlag::DebugLuauLogSolverToJsonFile && writeJsonLog)
            writeJsonLog(sourceModule.name, std::move(output));
        else
            printf("%s\n", output.c_str());
    }

    for (TypeError& e : cs.errors)
        module->errors.emplace_back(std::move(e));

    module->scopes = std::move(cg.scopes);
    module->type = sourceModule.type;
    module->upperBoundContributors = std::move(cs.upperBoundContributors);

    if (module->timeout || module->cancelled)
    {
        // If solver was interrupted, skip typechecking and replace all module
        // results with error-suppressing types to avoid leaking blocked/pending
        // types.
        ScopePtr moduleScope = module->getModuleScope();
        moduleScope->returnType = builtinTypes->errorTypePack;

        for (auto& [name, ty] : module->declaredGlobals)
            ty = builtinTypes->errorType;

        for (auto& [name, tf] : module->exportedTypeBindings)
            tf.type = builtinTypes->errorType;
    }
    else
    {
        try
        {
            switch (mode)
            {
            case Mode::Nonstrict:
                Luau::checkNonStrict(
                    builtinTypes,
                    NotNull{&typeFunctionRuntime},
                    iceHandler,
                    NotNull{&unifierState},
                    NotNull{&dfg},
                    NotNull{&limits},
                    sourceModule,
                    module.get()
                );
                break;

            case Mode::Definition:
                // fallthrough intentional
            case Mode::Strict:
                Luau::check(
                    builtinTypes,
                    NotNull{&typeFunctionRuntime},
                    NotNull{&unifierState},
                    NotNull{&limits},
                    logger.get(),
                    sourceModule,
                    module.get()
                );
                break;

            case Mode::NoCheck:
                break;
            };
        }
        catch (const TimeLimitError&)
        {
            module->timeout = true;
        }
        catch (const UserCancelError&)
        {
            module->cancelled = true;
        }

        if (FFlag::LuauExportValueSyntax &&
            FFlag::LuauExportValueTypecheck &&
            !module->timeout &&
            !module->cancelled)
        {
            synthesizeExportReturn(
                builtinTypes,
                NotNull{module.get()}
            );
        }
    }

    // If the only error we're producing is one about constraint solving being
    // incomplete, we can silence it.
    if (module->errors.size() == 1 &&
        get<ConstraintSolvingIncompleteError>(module->errors[0]) &&
        !FFlag::DebugLuauAlwaysShowConstraintSolvingIncomplete)
    {
        module->errors.clear();
    }

    ExpectedTypeVisitor etv{
        NotNull{&module->astTypes},
        NotNull{&module->astExpectedTypes},
        NotNull{&module->astResolvedTypes},
        NotNull{&module->astOverloadResolvedTypes},
        NotNull{&module->internalTypes},
        builtinTypes,
        NotNull{parentScope.get()}
    };

    sourceModule.root->visit(&etv);

    // NOTE: This used to be done prior to cloning the public interface, but
    // we now replace "internal" types with `*error-type*`.
    if (FFlag::DebugLuauForbidInternalTypes)
    {
        InternalTypeFinder finder;

        // `result->returnType` is not filled in yet, so we traverse the return
        // type of the root module.
        finder.traverse(module->getModuleScope()->returnType);

        for (const auto& [_, binding] : module->exportedTypeBindings)
            finder.traverse(binding.type);

        for (const auto& [_, ty] : module->astTypes)
            finder.traverse(ty);

        for (const auto& [_, ty] : module->astExpectedTypes)
            finder.traverse(ty);

        for (const auto& [_, tp] : module->astTypePacks)
            finder.traverse(tp);

        for (const auto& [_, ty] : module->astResolvedTypes)
            finder.traverse(ty);

        for (const auto& [_, ty] : module->astOverloadResolvedTypes)
            finder.traverse(ty);

        for (const auto& [_, tp] : module->astResolvedTypePacks)
            finder.traverse(tp);
    }

    unfreeze(module->interfaceTypes);

    module->clonePublicInterface(
        builtinTypes,
        *iceHandler,
        SolverMode::New
    );

    // It would be nice if we could freeze the arenas before doing type
    // checking, but we'll have to do some work to get there.
    //
    // TypeChecker2 sometimes needs to allocate TypePacks via extendTypePack()
    // in order to do its thing. We can rework that code to instead allocate
    // into a temporary arena as long as we can prove that the allocated types
    // and packs can never find their way into an error.
    //
    // Notably, we would first need to get to a place where TypeChecker2 is
    // never in the position of dealing with a FreeType. They should all be
    // bound to something by the time constraints are solved.
    freeze(module->internalTypes);
    freeze(module->interfaceTypes);

    return module;
}

ModulePtr Frontend::check(
    const SourceModule& sourceModule,
    Mode mode,
    std::vector<RequireCycle> requireCycles,
    std::optional<ScopePtr> environmentScope,
    bool forAutocomplete,
    bool recordJsonLog,
    Frontend::Stats& stats,
    TypeCheckLimits typeCheckLimits
)
{
    if (getLuauSolverMode() == SolverMode::New)
    {
        auto prepareModuleScopeWrap = [this, forAutocomplete](const ModuleName& name, const ScopePtr& scope)
        {
            if (prepareModuleScope)
                prepareModuleScope(name, scope, forAutocomplete);
        };

        try
        {
            return Luau::check(
                sourceModule,
                mode,
                requireCycles,
                builtinTypes,
                NotNull{&iceHandler},
                NotNull{forAutocomplete ? &moduleResolverForAutocomplete : &moduleResolver},
                NotNull{fileResolver},
                environmentScope ? *environmentScope : globals.globalScope,
                globals.globalTypeFunctionScope,
                prepareModuleScopeWrap,
                options,
                std::move(typeCheckLimits),
                recordJsonLog,
                stats,
                writeJsonLog
            );
        }
        catch (const InternalCompilerError& err)
        {
            InternalCompilerError augmented = err.location.has_value() ? InternalCompilerError{err.message, sourceModule.name, *err.location}
                                                                       : InternalCompilerError{err.message, sourceModule.name};
            throw augmented;
        }
    }
    else
    {
        TypeChecker typeChecker(
            forAutocomplete ? globalsForAutocomplete.globalScope : globals.globalScope,
            forAutocomplete ? &moduleResolverForAutocomplete : &moduleResolver,
            builtinTypes,
            &iceHandler
        );

        if (prepareModuleScope)
        {
            typeChecker.prepareModuleScope = [this, forAutocomplete](const ModuleName& name, const ScopePtr& scope)
            {
                prepareModuleScope(name, scope, forAutocomplete);
            };
        }

        typeChecker.requireCycles = requireCycles;
        typeChecker.finishTime = typeCheckLimits.finishTime;
        typeChecker.instantiationChildLimit = typeCheckLimits.instantiationChildLimit;
        typeChecker.unifierIterationLimit = typeCheckLimits.unifierIterationLimit;
        typeChecker.cancellationToken = typeCheckLimits.cancellationToken;

        return typeChecker.check(sourceModule, mode, std::move(environmentScope));
    }
}

// Read AST into sourceModules if necessary.  Trace require()s.  Report parse errors.
std::pair<SourceNode*, SourceModule*> Frontend::getSourceNode(const ModuleName& name, const TypeCheckLimits& limits)
{
    auto it = sourceNodes.find(name);
    if (it != sourceNodes.end() && !it->second->hasDirtySourceModule())
    {
        auto moduleIt = sourceModules.find(name);
        if (moduleIt != sourceModules.end())
            return {it->second.get(), moduleIt->second.get()};
        else
        {
            LUAU_ASSERT(!"Everything in sourceNodes should also be in sourceModules");
            return {it->second.get(), nullptr};
        }
    }

    LUAU_TIMETRACE_SCOPE("Frontend::getSourceNode", "Frontend");
    LUAU_TIMETRACE_ARGUMENT("name", name.c_str());

    double timestamp = getTimestamp();

    std::optional<SourceCode> source = fileResolver->readSource(name);
    std::optional<std::string> environmentName = fileResolver->getEnvironmentForModule(name);

    stats.timeRead += getTimestamp() - timestamp;

    if (!source)
    {
        sourceModules.erase(name);
        return {nullptr, nullptr};
    }

    const Config& config = configResolver->getConfig(name, limits);
    ParseOptions opts = config.parseOptions;
    opts.captureComments = true;
    SourceModule result = parse(name, source->source, opts);
    result.type = source->type;

    RequireTraceResult& require = requireTrace[name];
    require = traceRequires(fileResolver, result.root, name, limits);

    std::shared_ptr<SourceNode>& sourceNode = sourceNodes[name];

    if (!sourceNode)
        sourceNode = std::make_shared<SourceNode>();

    std::shared_ptr<SourceModule>& sourceModule = sourceModules[name];

    if (!sourceModule)
        sourceModule = std::make_shared<SourceModule>();

    *sourceModule = std::move(result);
    sourceModule->environmentName = environmentName;

    sourceNode->name = sourceModule->name;
    sourceNode->humanReadableName = sourceModule->humanReadableName;

    // clear all prior dependents. we will re-add them after parsing the rest of the graph
    for (const auto& [moduleName, _] : sourceNode->requireLocations)
    {
        if (auto depIt = sourceNodes.find(moduleName); depIt != sourceNodes.end())
            depIt->second->dependents.erase(sourceNode->name);
    }

    sourceNode->requireSet.clear();
    sourceNode->requireLocations.clear();
    sourceNode->dirtySourceModule = false;

    if (it == sourceNodes.end())
    {
        sourceNode->dirtyModule = true;
        sourceNode->dirtyModuleForAutocomplete = true;
    }

    for (const auto& [moduleName, location] : require.requireList)
        sourceNode->requireSet.insert(moduleName);

    sourceNode->requireLocations = require.requireList;

    return {sourceNode.get(), sourceModule.get()};
}

/** Try to parse a source file into a SourceModule.
 *
 * The logic here is a little bit more complicated than we'd like it to be.
 *
 * If a file does not exist, we return none to prevent the Frontend from creating knowledge that this module exists.
 * If the Frontend thinks that the file exists, it will not produce an "Unknown require" error.
 *
 * If the file has syntax errors, we report them and synthesize an empty AST if it's not available.
 * This suppresses the Unknown require error and allows us to make a best effort to typecheck code that require()s
 * something that has broken syntax.
 * We also translate Luau::ParseError into a Luau::TypeError so that we can use a vector<TypeError> to describe the
 * result of the check()
 */
SourceModule Frontend::parse(const ModuleName& name, std::string_view src, const ParseOptions& parseOptions)
{
    LUAU_TIMETRACE_SCOPE("Frontend::parse", "Frontend");
    LUAU_TIMETRACE_ARGUMENT("name", name.c_str());

    SourceModule sourceModule;

    double timestamp = getTimestamp();

    Luau::ParseResult parseResult = Luau::Parser::parse(src.data(), src.size(), *sourceModule.names, *sourceModule.allocator, parseOptions);

    stats.timeParse += getTimestamp() - timestamp;
    stats.files++;
    stats.lines += parseResult.lines;

    if (!parseResult.errors.empty())
        sourceModule.parseErrors.insert(sourceModule.parseErrors.end(), parseResult.errors.begin(), parseResult.errors.end());

    if (parseResult.errors.empty() || parseResult.root)
    {
        sourceModule.root = parseResult.root;
        sourceModule.mode = parseMode(parseResult.hotcomments);
    }
    else
    {
        sourceModule.root = sourceModule.allocator->alloc<AstStatBlock>(Location{}, AstArray<AstStat*>{nullptr, 0});
        sourceModule.mode = Mode::NoCheck;
    }

    sourceModule.name = name;
    sourceModule.humanReadableName = fileResolver->getHumanReadableModuleName(name);

    if (parseOptions.captureComments)
    {
        sourceModule.commentLocations = std::move(parseResult.commentLocations);
        sourceModule.hotcomments = std::move(parseResult.hotcomments);
    }

    return sourceModule;
}


FrontendModuleResolver::FrontendModuleResolver(Frontend* frontend)
    : frontend(frontend)
{
}

std::optional<ModuleInfo> FrontendModuleResolver::resolveModuleInfo(const ModuleName& currentModuleName, const AstExpr& pathExpr)
{
    // FIXME I think this can be pushed into the FileResolver.
    auto it = frontend->requireTrace.find(currentModuleName);
    if (it == frontend->requireTrace.end())
    {
        // CLI-43699
        // If we can't find the current module name, that's because we bypassed the frontend's initializer
        // and called typeChecker.check directly.
        // In that case, requires will always fail.
        return std::nullopt;
    }

    const auto& exprs = it->second.exprs;

    const ModuleInfo* info = exprs.find(&pathExpr);
    if (!info)
        return std::nullopt;

    return *info;
}

const ModulePtr FrontendModuleResolver::getModule(const ModuleName& moduleName) const
{
    std::scoped_lock lock(moduleMutex);

    auto it = modules.find(moduleName);
    if (it != modules.end())
        return it->second;
    else
        return nullptr;
}

bool FrontendModuleResolver::moduleExists(const ModuleName& moduleName) const
{
    return frontend->sourceNodes.count(moduleName) != 0;
}

std::string FrontendModuleResolver::getHumanReadableModuleName(const ModuleName& moduleName) const
{
    return frontend->fileResolver->getHumanReadableModuleName(moduleName);
}

bool FrontendModuleResolver::setModule(const ModuleName& moduleName, ModulePtr module)
{
    std::scoped_lock lock(moduleMutex);

    bool replaced = modules.count(moduleName) > 0;
    modules[moduleName] = std::move(module);
    return replaced;
}

void FrontendModuleResolver::clearModules()
{
    std::scoped_lock lock(moduleMutex);

    modules.clear();
}

void Frontend::clearStats()
{
    stats = {};
}

void Frontend::clear()
{
    sourceNodes.clear();
    sourceModules.clear();
    requireTrace.clear();

    moduleResolver.clearModules();
    moduleResolverForAutocomplete.clearModules();

    sccs.clear();

    moduleQueue.clear();

    clearStats();
}

void Frontend::clearBuiltinEnvironments()
{
    environments.clear();
    builtinDefinitions.clear();
}

ScopePtr Frontend::addEnvironment(const std::string& environmentName)
{
    auto it = environments.find(environmentName);

    if (it != environments.end())
        return it->second;

    ScopePtr scope = std::make_shared<Scope>(builtinTypes->anyTypePack);

    environments[environmentName] = scope;

    return scope;
}

ScopePtr Frontend::getEnvironmentScope(const std::string& environmentName) const
{
    auto it = environments.find(environmentName);

    if (it == environments.end())
        return nullptr;

    return it->second;
}

void Frontend::registerBuiltinDefinition(const std::string& name, std::function<void(Frontend&, GlobalTypes&, ScopePtr)> callback)
{
    builtinDefinitions[name] = std::move(callback);
}

void Frontend::applyBuiltinDefinitionToEnvironment(const std::string& environmentName, const std::string& definitionName)
{
    auto definitionIt = builtinDefinitions.find(definitionName);

    if (definitionIt == builtinDefinitions.end())
    {
        return;
    }

    ScopePtr environment = getEnvironmentScope(environmentName);

    if (!environment)
    {
        environment = addEnvironment(environmentName);
    }

    definitionIt->second(*this, globals, environment);
}

void Frontend::queueModuleCheck(const std::vector<ModuleName>& names)
{
    for (const ModuleName& name : names)
    {
        moduleQueue.push_back(name);
    }
}

void Frontend::queueModuleCheck(const ModuleName& name)
{
    moduleQueue.push_back(name);
}

std::vector<ModuleName> Frontend::checkQueuedModules(
    std::optional<FrontendOptions> optionOverride,
    std::function<void(std::vector<std::function<void()>> tasks)> executeTasks,
    std::function<bool(size_t done, size_t total)> progress
)
{
    FrontendOptions frontendOptions = optionOverride.value_or(options);

    if (getLuauSolverMode() == SolverMode::New)
        frontendOptions.forAutocomplete = false;

    // By taking data into locals, we make sure queue is cleared at the end,
    // even if an ICE or a different exception is thrown.
    std::vector<ModuleName> currModuleQueue;
    std::swap(currModuleQueue, moduleQueue);

    DenseHashSet<Luau::ModuleName> seen{{}};

    std::shared_ptr<BuildQueueWorkState> state =
        std::make_shared<BuildQueueWorkState>();

    for (const ModuleName& name : currModuleQueue)
    {
        if (seen.contains(name))
            continue;

        if (!isDirty(name, frontendOptions.forAutocomplete))
        {
            seen.insert(name);
            continue;
        }

        std::vector<ModuleName> queue;

        bool cycleDetected = parseGraph(
            queue,
            name,
            makeTypeCheckLimits(frontendOptions),
            frontendOptions.forAutocomplete,
            [&seen](const ModuleName& name)
            {
                return seen.contains(name);
            }
        );

        addBuildQueueItems(
            state->buildQueueItems,
            queue,
            cycleDetected,
            seen,
            frontendOptions
        );
    }

    if (state->buildQueueItems.empty())
        return {};

    // Map every module name to the build queue item containing it.
    //
    // A BuildQueueItem may represent several modules when those modules
    // belong to an SCC, so we cannot map only one name per item.
    std::unordered_map<ModuleName, size_t> moduleNameToQueue;

    for (size_t i = 0; i < state->buildQueueItems.size(); i++)
    {
        BuildQueueItem& item = state->buildQueueItems[i];

        for (const BuildQueueModuleInfo& moduleInfo : item.modules)
            moduleNameToQueue[moduleInfo.name] = i;
    }

    // Default task execution is single-threaded and immediate.
    if (!executeTasks)
    {
        executeTasks = [](std::vector<std::function<void()>> tasks)
        {
            for (auto& task : tasks)
                task();
        };
    }

    state->executeTasks = executeTasks;
    state->remaining = state->buildQueueItems.size();

    // Record dependencies between build queue items.
    //
    // Both runtime requires and type-only requires participate in the
    // scheduling dependency graph. A type-only dependency must therefore
    // wait for its target module/SCC to be checked before the dependent
    // module/SCC can be checked.
    for (size_t i = 0; i < state->buildQueueItems.size(); i++)
    {
        BuildQueueItem& item = state->buildQueueItems[i];

        // An SCC item may contain multiple modules, so inspect every
        // module represented by this queue item.
        for (const BuildQueueModuleInfo& moduleInfo : item.modules)
        {
            auto processDependencies = [&](const DenseHashSet<ModuleName>& dependencies)
            {
                for (const ModuleName& dep : dependencies)
                {
                    auto sourceNodeIt = sourceNodes.find(dep);

                    if (sourceNodeIt == sourceNodes.end())
                        continue;

                    if (!sourceNodeIt->second->hasDirtyModule(frontendOptions.forAutocomplete))
                        continue;

                    auto queueIt = moduleNameToQueue.find(dep);

                    // The dependency may have been dirty when the graph was
                    // constructed but may not belong to the current build
                    // queue. In that case there is nothing to wait for.
                    if (queueIt == moduleNameToQueue.end())
                        continue;

                    size_t dependencyQueueIndex = queueIt->second;

                    // A module inside the same SCC is not a pending
                    // dependency of itself. The SCC must be processed as
                    // one queue item.
                    if (dependencyQueueIndex == i)
                        continue;

                    item.dirtyDependencies++;

                    state->buildQueueItems[dependencyQueueIndex]
                        .reverseDeps.push_back(i);
                }
            };

            processDependencies(moduleInfo.sourceNode->requireSet);

            if (FFlag::LuauCyclicRequireTypeInference)
                processDependencies(moduleInfo.sourceNode->typeRequireSet);
        }
    }

    std::vector<size_t> nextItems;

    // In the first pass, check all modules with no pending dependencies.
    for (size_t i = 0; i < state->buildQueueItems.size(); i++)
    {
        if (state->buildQueueItems[i].dirtyDependencies == 0)
            nextItems.push_back(i);
    }

    if (!nextItems.empty())
    {
        sendQueueItemTasks(state, nextItems);
        nextItems.clear();
    }

    // If not a single item was found, a cycle in the graph was hit.
    if (state->processing == 0)
        sendQueueCycleItemTask(state);

    std::optional<size_t> itemWithException;
    bool cancelled = false;

    while (state->remaining != 0)
    {
        {
            std::unique_lock guard(state->mtx);

            // If nothing is ready yet, wait.
            state->cv.wait(
                guard,
                [state]
                {
                    return !state->readyQueueItems.empty();
                }
            );

            // Handle checked items.
            for (size_t i : state->readyQueueItems)
            {
                const BuildQueueItem& item = state->buildQueueItems[i];

                // If an exception was thrown, stop adding new items and
                // wait for processing items to complete.
                if (item.exception)
                    itemWithException = i;

                // An SCC item can contain several modules. Cancellation of
                // any module cancels the corresponding queue item.
                for (const BuildQueueModuleInfo& moduleInfo : item.modules)
                {
                    if (moduleInfo.module && moduleInfo.module->cancelled)
                    {
                        cancelled = true;
                        break;
                    }
                }

                if (itemWithException || cancelled)
                    break;

                recordItemResult(item);

                // Notify items that were waiting for this dependency.
                for (size_t reverseDep : item.reverseDeps)
                {
                    BuildQueueItem& reverseDepItem =
                        state->buildQueueItems[reverseDep];

                    LUAU_ASSERT(reverseDepItem.dirtyDependencies != 0);
                    reverseDepItem.dirtyDependencies--;

                    // In case of a module cycle earlier, check if this
                    // unlocked an item that was already processed.
                    if (!reverseDepItem.processing &&
                        reverseDepItem.dirtyDependencies == 0)
                    {
                        nextItems.push_back(reverseDep);
                    }
                }
            }

            LUAU_ASSERT(
                state->processing >= state->readyQueueItems.size()
            );

            state->processing -= state->readyQueueItems.size();

            LUAU_ASSERT(
                state->remaining >= state->readyQueueItems.size()
            );

            state->remaining -= state->readyQueueItems.size();
            state->readyQueueItems.clear();
        }

        if (progress)
        {
            if (!progress(
                    state->buildQueueItems.size() - state->remaining,
                    state->buildQueueItems.size()))
            {
                cancelled = true;
            }
        }

        // Items cannot be submitted while holding the lock.
        if (!nextItems.empty())
        {
            sendQueueItemTasks(state, nextItems);
            nextItems.clear();
        }

        if (state->processing == 0)
        {
            // Typechecking might have been cancelled by the user, don't
            // return partial results.
            if (cancelled)
                return {};

            // We might have stopped because of a pending exception.
            if (itemWithException)
                recordItemResult(
                    state->buildQueueItems[*itemWithException]
                );
        }

        // If we aren't done, but don't have anything processing, we hit
        // a cycle.
        if (state->remaining != 0 && state->processing == 0)
            sendQueueCycleItemTask(state);
    }

    std::vector<ModuleName> checkedModules;

    for (const BuildQueueItem& item : state->buildQueueItems)
    {
        checkedModules.reserve(
            checkedModules.size() + item.modules.size()
        );

        for (const BuildQueueModuleInfo& moduleInfo : item.modules)
            checkedModules.push_back(moduleInfo.name);
    }

    return checkedModules;
}

std::optional<CheckResult> Frontend::getCheckResult(const ModuleName& name, bool accumulateNested, bool forAutocomplete)
{
    if (getLuauSolverMode() == SolverMode::New)
        forAutocomplete = false;

    auto it = sourceNodes.find(name);

    if (it == sourceNodes.end() || it->second->hasDirtyModule(forAutocomplete))
    {
        return std::nullopt;
    }

    auto& resolver = forAutocomplete ? moduleResolverForAutocomplete : moduleResolver;

    ModulePtr module = resolver.getModule(name);

    if (module == nullptr)
    {
        throw InternalCompilerError("Frontend does not have module: " + name, name);
    }

    CheckResult checkResult;

    if (module->timeout)
        checkResult.timeoutHits.push_back(name);

    if (accumulateNested)
    {
        checkResult.errors = accumulateErrors(sourceNodes, resolver, name);
    }
    else
    {
        checkResult.errors.insert(checkResult.errors.end(), module->errors.begin(), module->errors.end());
    }

    checkResult.lintResult = module->lintResult;

    return checkResult;
}

std::vector<ModuleName> Frontend::getRequiredScripts(const ModuleName& name, const TypeCheckLimits& limits)
{
    RequireTraceResult require = requireTrace[name];

    if (isDirty(name))
    {
        std::optional<SourceCode> source = fileResolver->readSource(name);

        if (!source)
            return {};

        const Config& config = configResolver->getConfig(name, limits);

        ParseOptions opts = config.parseOptions;

        opts.captureComments = true;

        SourceModule result = parse(name, source->source, opts);

        result.type = source->type;

        require = traceRequires(fileResolver, result.root, name, limits);
    }

    std::vector<std::string> requiredModuleNames;

    requiredModuleNames.reserve(require.requireList.size());

    for (const auto& [moduleName, _] : require.requireList)
    {
        requiredModuleNames.push_back(moduleName);
    }

    return requiredModuleNames;
}

bool Frontend::parseGraph(
    std::vector<ModuleName>& buildQueue,
    const ModuleName& root,
    const TypeCheckLimits& limits,
    bool forAutocomplete,
    std::function<bool(const ModuleName&)> canSkip
)
{
    LUAU_TIMETRACE_SCOPE("Frontend::parseGraph", "Frontend");

    LUAU_TIMETRACE_ARGUMENT("root", root.c_str());

    enum Mark
    {
        None,
        Temporary,
        Permanent
    };

    DenseHashMap<SourceNode*, Mark> seen;

    std::vector<SourceNode*> stack;
    std::vector<SourceNode*> path;

    bool cyclic = false;

    {
        auto [sourceNode, _] = getSourceNode(root, limits);

        if (sourceNode)
            stack.push_back(sourceNode);
    }

    while (!stack.empty())
    {
        SourceNode* top = stack.back();

        stack.pop_back();

        if (top == nullptr)
        {
            LUAU_ASSERT(!path.empty());

            top = path.back();

            path.pop_back();

            Mark& topseen = seen[top];

            LUAU_ASSERT(topseen == Temporary);

            topseen = Permanent;

            buildQueue.push_back(top->name);

            for (const ModuleName& dep : top->requireSet)
            {
                if (auto it = sourceNodes.find(dep); it != sourceNodes.end())
                {
                    it->second->dependents.insert(top->name);
                }
            }

            for (const ModuleName& dep : top->typeRequireSet)
            {
                if (auto it = sourceNodes.find(dep); it != sourceNodes.end())
                {
                    it->second->typeDependents.insert(top->name);
                }
            }
        }
        else
        {
            Mark& topseen = seen[top];

            if (topseen != None)
                continue;

            topseen = Temporary;

            stack.push_back(nullptr);
            path.push_back(top);

            auto processDependencies = [&](const DenseHashSet<ModuleName>& dependencies, bool runtime)
            {
                for (const ModuleName& dep : dependencies)
                {
                    auto it = sourceNodes.find(dep);

                    if (it != sourceNodes.end())
                    {
                        if (!it->second->hasDirtyModule(forAutocomplete))
                        {
                            continue;
                        }

                        if (canSkip && canSkip(dep))
                        {
                            continue;
                        }

                        if (seen.contains(it->second.get()))
                        {
                            if (runtime && seen[it->second.get()] == Temporary)
                            {
                                cyclic = true;
                            }

                            stack.push_back(it->second.get());

                            continue;
                        }
                    }

                    auto [sourceNode, _] = getSourceNode(dep, limits);

                    if (sourceNode)
                    {
                        stack.push_back(sourceNode);

                        seen[sourceNode] = None;
                    }
                }
            };

            processDependencies(top->requireSet, true);

            processDependencies(top->typeRequireSet, false);
        }
    }

    return cyclic;
}

static bool moduleHasTopLevelReturn(const SourceModule& sourceModule)
{
    if (!sourceModule.root)
        return false;

    for (AstStat* stat : sourceModule.root->body)
    {
        if (stat->is<AstStatReturn>())
            return true;
    }

    return false;
}

template<typename GetDependencies>
static std::vector<ModuleSCCPtr> computeTarjanSCCs(
    const std::vector<ModuleName>& buildQueue,
    const std::unordered_map<ModuleName, std::shared_ptr<SourceNode>>& sourceNodes,
    GetDependencies getDependencies
)
{
    const size_t N = buildQueue.size();

    if (N == 0)
        return {};

    DenseHashMap<ModuleName, size_t> nameToVertex{nullptr};

    for (size_t i = 0; i < N; i++)
        nameToVertex[buildQueue[i]] = i;

    std::vector<size_t> edges;

    std::vector<size_t> edgeStart(N + 1, 0);

    for (size_t v = 0; v < N; v++)
    {
        edgeStart[v] = edges.size();

        auto nodeIt = sourceNodes.find(buildQueue[v]);

        if (nodeIt != sourceNodes.end())
        {
            getDependencies(
                *nodeIt->second,
                [&](const ModuleName& dep)
                {
                    if (size_t* idx = nameToVertex.find(dep))
                    {
                        edges.push_back(*idx);
                    }
                }
            );
        }
    }

    edgeStart[N] = edges.size();

    struct TarjanNode
    {
        int index = -1;
        int lowlink = 0;
        bool onStack = false;
    };

    struct TarjanFrame
    {
        size_t vertex;
        size_t edgeCursor;
    };

    std::vector<TarjanNode> nodes(N);

    std::vector<TarjanFrame> worklist;

    std::vector<size_t> moduleStack;

    int nextIndex = 0;

    std::vector<ModuleSCCPtr> result;

    for (size_t start = 0; start < N; start++)
    {
        if (nodes[start].index != -1)
        {
            continue;
        }

        worklist.push_back(TarjanFrame{start, edgeStart[start]});

        nodes[start].index = nodes[start].lowlink = nextIndex++;

        nodes[start].onStack = true;

        moduleStack.push_back(start);

        while (!worklist.empty())
        {
            TarjanFrame& frame = worklist.back();

            size_t v = frame.vertex;

            if (frame.edgeCursor < edgeStart[v + 1])
            {
                size_t w = edges[frame.edgeCursor++];

                if (nodes[w].index == -1)
                {
                    worklist.push_back(TarjanFrame{w, edgeStart[w]});

                    nodes[w].index = nodes[w].lowlink = nextIndex++;

                    nodes[w].onStack = true;

                    moduleStack.push_back(w);
                }
                else if (nodes[w].onStack)
                {
                    nodes[v].lowlink = std::min(nodes[v].lowlink, nodes[w].index);
                }
            }
            else
            {
                if (nodes[v].lowlink == nodes[v].index)
                {
                    auto scc = std::make_shared<ModuleSCC>();

                    size_t w;

                    do
                    {
                        w = moduleStack.back();

                        moduleStack.pop_back();

                        nodes[w].onStack = false;

                        scc->members.push_back(buildQueue[w]);
                    } while (w != v);

                    if (scc->members.size() > 1)
                    {
                        result.push_back(scc);
                    }
                    else if (scc->members.size() == 1)
                    {
                        const ModuleName& only = scc->members[0];

                        auto nodeIt = sourceNodes.find(only);

                        if (nodeIt != sourceNodes.end())
                        {
                            bool selfCycle = false;

                            getDependencies(
                                *nodeIt->second,
                                [&](const ModuleName& dep)
                                {
                                    if (dep == only)
                                    {
                                        selfCycle = true;
                                    }
                                }
                            );

                            if (selfCycle)
                            {
                                result.push_back(scc);
                            }
                        }
                    }
                }

                worklist.pop_back();

                if (!worklist.empty())
                {
                    nodes[worklist.back().vertex].lowlink = std::min(nodes[worklist.back().vertex].lowlink, nodes[v].lowlink);
                }
            }
        }
    }

    return result;
}

void Frontend::computeSCCs(const std::vector<ModuleName>& buildQueue)
{
    LUAU_ASSERT(FFlag::LuauCyclicRequireTypeInference);

    for (const ModuleName& name : buildQueue)
    {
        auto it = sourceNodes.find(name);

        if (it != sourceNodes.end())
        {
            it->second->scc.reset();
        }
    }

    sccs.clear();

    std::vector<ModuleSCCPtr> foundSCCs = computeTarjanSCCs(
        buildQueue,
        sourceNodes,
        [](const SourceNode& sourceNode, auto process)
        {
            for (const ModuleName& dep : sourceNode.requireSet)
            {
                process(dep);
            }

            for (const ModuleName& dep : sourceNode.typeRequireSet)
            {
                process(dep);
            }
        }
    );

    for (const ModuleSCCPtr& scc : foundSCCs)
    {
        bool allMembersAreValid = true;

        for (const ModuleName& member : scc->members)
        {
            auto sourceModuleIt = sourceModules.find(member);

            if (sourceModuleIt == sourceModules.end() || !sourceModuleIt->second || moduleHasTopLevelReturn(*sourceModuleIt->second))
            {
                allMembersAreValid = false;

                break;
            }
        }

        if (!allMembersAreValid)
            continue;

        for (const ModuleName& member : scc->members)
        {
            sccs[member] = scc;

            auto nodeIt = sourceNodes.find(member);

            LUAU_ASSERT(nodeIt != sourceNodes.end());

            nodeIt->second->scc = scc;
        }
    }
}

void Frontend::addBuildQueueItems(
    std::vector<BuildQueueItem>& items,
    std::vector<ModuleName>& buildQueue,
    bool cycleDetected,
    DenseHashSet<Luau::ModuleName>& seen,
    const FrontendOptions& frontendOptions
)
{
    DenseHashMap<ModuleSCC*, size_t> sccToItemIndex{nullptr};

    for (const ModuleName& moduleName : buildQueue)
    {
        if (seen.contains(moduleName))
            continue;

        seen.insert(moduleName);

        LUAU_ASSERT(sourceNodes.count(moduleName));

        std::shared_ptr<SourceNode>& sourceNode = sourceNodes[moduleName];

        if (!sourceNode->hasDirtyModule(frontendOptions.forAutocomplete))
            continue;

        LUAU_ASSERT(sourceModules.count(moduleName));

        std::shared_ptr<SourceModule>& sourceModule = sourceModules[moduleName];

        BuildQueueModuleInfo moduleInfo{
            moduleName,
            fileResolver->getHumanReadableModuleName(moduleName),
            sourceNode,
            sourceModule,
        };

        moduleInfo.config =
            configResolver->getConfig(moduleName, makeTypeCheckLimits(frontendOptions));

        moduleInfo.environmentScope =
            getModuleEnvironment(
                *sourceModule,
                moduleInfo.config,
                frontendOptions.forAutocomplete
            );

        if (cycleDetected)
        {
            moduleInfo.requireCycles =
                getRequireCycles(fileResolver, sourceNodes, sourceNode.get());
        }

        sourceModule->cyclic = !moduleInfo.requireCycles.empty();

        if (FFlag::LuauCyclicRequireTypeInference)
        {
            if (ModuleSCCPtr* sccPtr = sccs.find(moduleName))
            {
                ModuleSCCPtr scc = *sccPtr;

                if (
                    getLuauSolverMode() == SolverMode::New &&
                    !FFlag::DebugLuauForceOldSolver
                )
                {
                    if (!scc->sharedArena)
                    {
                        scc->sharedArena = std::make_shared<TypeArena>();

                        for (const ModuleName& member : scc->members)
                        {
                            TypeId placeholderReturnType =
                                scc->sharedArena->addType(BlockedType{});

                            TypePackId placeholderPack =
                                scc->sharedArena->addTypePack({placeholderReturnType});

                            ModulePtr placeholderModule =
                                std::make_shared<Module>();

                            placeholderModule->name = member;
                            placeholderModule->humanReadableName =
                                fileResolver->getHumanReadableModuleName(member);
                            placeholderModule->type = SourceCode::Type::Module;
                            placeholderModule->mode = Mode::Strict;
                            placeholderModule->returnType = placeholderPack;

                            ScopePtr placeholderScope =
                                std::make_shared<Scope>(builtinTypes->anyTypePack);

                            placeholderScope->returnType = placeholderPack;

                            placeholderModule->scopes.emplace_back(
                                Location{},
                                placeholderScope
                            );

                            moduleResolver.setModule(
                                member,
                                std::move(placeholderModule)
                            );
                        }
                    }

                    if (size_t* existingIdx = sccToItemIndex.find(scc.get()))
                    {
                        items[*existingIdx].modules.emplace_back(
                            std::move(moduleInfo)
                        );
                    }
                    else
                    {
                        BuildQueueItem data;

                        data.options = frontendOptions;
                        data.recordJsonLog =
                            FFlag::DebugLuauLogSolverToJson;
                        data.scc = scc;

                        data.modules.emplace_back(
                            std::move(moduleInfo)
                        );

                        sccToItemIndex[scc.get()] = items.size();

                        items.push_back(std::move(data));
                    }

                    continue;
                }
            }
        }

        BuildQueueItem data;

        data.options = frontendOptions;
        data.recordJsonLog =
            FFlag::DebugLuauLogSolverToJson;

        data.modules.emplace_back(
            std::move(moduleInfo)
        );

        items.push_back(std::move(data));
    }
}

static void applyInternalLimitScaling(SourceNode& sourceNode, const ModulePtr module, double limit)
{
    if (module->timeout)
    {
        sourceNode.autocompleteLimitsMult = sourceNode.autocompleteLimitsMult / 2.0;
    }
    else if (module->checkDurationSec < limit / 2.0)
    {
        sourceNode.autocompleteLimitsMult = std::min(sourceNode.autocompleteLimitsMult * 2.0, 1.0);
    }
}

struct CyclicTopLevelAccessVisitor : public AstVisitor
{
    NotNull<const DenseHashMap<Name, ModuleName>> peerImports;

    NotNull<std::vector<TypeError>> errors;

    ModuleName moduleName;

    CyclicTopLevelAccessVisitor(
        NotNull<const DenseHashMap<Name, ModuleName>> peerImports,
        NotNull<std::vector<TypeError>> errors,
        ModuleName moduleName
    )
        : peerImports(peerImports)
        , errors(errors)
        , moduleName(std::move(moduleName))
    {
    }

    bool visit(AstExprFunction*) override
    {
        return false;
    }

    bool visit(AstExprIndexName* node) override
    {
        if (auto* local = node->expr->as<AstExprLocal>())
        {
            if (const ModuleName* target = peerImports->find(local->local->name.value))
            {
                errors->emplace_back(
                    node->location,
                    moduleName,
                    CyclicModuleTopLevelAccess{*target, std::string{local->local->name.value}, std::string{node->index.value}}
                );
            }
        }

        return true;
    }

    bool visit(AstExprIndexExpr* node) override
    {
        if (auto* local = node->expr->as<AstExprLocal>())
        {
            if (const ModuleName* target = peerImports->find(local->local->name.value))
            {
                std::string propName;

                if (auto* constStr = node->index->as<AstExprConstantString>())
                {
                    propName = std::string{constStr->value.data, constStr->value.size};
                }

                errors->emplace_back(
                    node->location, moduleName, CyclicModuleTopLevelAccess{*target, std::string{local->local->name.value}, std::move(propName)}
                );
            }
        }

        return true;
    }
};

static void errorOnCyclicTopLevelAccess(const SourceModule& sourceModule, const ModulePtr& module, const std::vector<ModuleName>& sccMembers)
{
    LUAU_ASSERT(FFlag::LuauCyclicRequireTopLevelAccessError);

    ScopePtr rootScope = module->getModuleScope();

    if (!rootScope || rootScope->importedModules.empty())
    {
        return;
    }

    DenseHashSet<ModuleName> peerSet{{}};

    for (const ModuleName& member : sccMembers)
    {
        if (member != sourceModule.name)
        {
            peerSet.insert(member);
        }
    }

    if (peerSet.empty())
        return;

    DenseHashMap<Name, ModuleName> peerImports{{}};

    for (const auto& [localName, importedModule] : rootScope->importedModules)
    {
        if (peerSet.contains(importedModule))
        {
            peerImports[localName] = importedModule;
        }
    }

    if (peerImports.empty())
        return;

    CyclicTopLevelAccessVisitor visitor{NotNull{&peerImports}, NotNull{&module->errors}, sourceModule.name};

    for (AstStat* stat : sourceModule.root->body)
    {
        stat->visit(&visitor);
    }
}

void Frontend::checkSCCBuildQueueItem(BuildQueueItem& item)
{
    ModuleSCCPtr scc = item.scc;

    LUAU_ASSERT(scc->sharedArena);

    TypeCheckLimits typeCheckLimits =
        makeTypeCheckLimits(item.options);

    UnifierSharedState unifierState{
        NotNull{&iceHandler}
    };

    unifierState.counters.recursionLimit =
        FInt::LuauTypeInferRecursionLimit;

    unifierState.counters.iterationLimit =
        typeCheckLimits.unifierIterationLimit.value_or(
            FInt::LuauTypeInferIterationLimit
        );

    Normalizer normalizer{
        scc->sharedArena.get(),
        builtinTypes,
        NotNull{&unifierState},
        SolverMode::New
    };

    TypeFunctionRuntime typeFunctionRuntime{
        NotNull{&iceHandler},
        NotNull{&typeCheckLimits}
    };

    typeFunctionRuntime.allowEvaluation = true;

    struct SCCModuleCGData
    {
        std::unique_ptr<DataFlowGraph> dfg;
        std::vector<std::pair<Location, ScopePtr>> cgScopes;
    };

    std::vector<SCCModuleCGData> cgData(item.modules.size());

    std::unique_ptr<ConstraintGraph> cgraph =
        std::make_unique<ConstraintGraph>(builtinTypes);

    std::vector<TypeError> mergedErrors;
    std::vector<ConstraintPtr> mergedConstraints;
    std::vector<ConstraintPtr> mergedDeferredConstraints;

    for (size_t i = 0; i < item.modules.size(); i++)
    {
        BuildQueueModuleInfo& moduleInfo = item.modules[i];

        const SourceModule& sourceModule =
            *moduleInfo.sourceModule;

        const Config& config =
            moduleInfo.config;

        Mode mode;

        if (FFlag::DebugLuauForceStrictMode)
        {
            mode = Mode::Strict;
        }
        else if (FFlag::DebugLuauForceNonStrictMode)
        {
            mode = Mode::Nonstrict;
        }
        else
        {
            mode = sourceModule.mode.value_or(config.mode);
        }

        moduleInfo.sourceModule->mode = {mode};

        ModulePtr module =
            std::make_shared<Module>();

        module->checkedInNewSolver = true;
        module->name = sourceModule.name;
        module->humanReadableName =
            sourceModule.humanReadableName;
        module->mode = mode;

        // Luau 0.729 owns these arenas directly.
        module->internalTypes.owningModule =
            module.get();

        module->interfaceTypes.owningModule =
            module.get();

        module->allocator =
            sourceModule.allocator;

        module->names =
            sourceModule.names;

        module->root =
            sourceModule.root;

        iceHandler.moduleName =
            sourceModule.name;

        cgData[i].dfg =
            std::make_unique<DataFlowGraph>(
                DataFlowGraphBuilder::build(
                    sourceModule.root,
                    NotNull{&module->defArena},
                    NotNull{&module->keyArena},
                    NotNull{&iceHandler}
                )
            );

        ScopePtr environmentScope =
            moduleInfo.environmentScope;

        auto prepareModuleScopeWrap =
            [this](
                const ModuleName& name,
                const ScopePtr& scope
            )
            {
                if (prepareModuleScope)
                {
                    prepareModuleScope(
                        name,
                        scope,
                        false
                    );
                }
            };

        ConstraintGenerator cg{
            module,
            NotNull{&normalizer},
            NotNull{&typeFunctionRuntime},
            NotNull<ModuleResolver>{&moduleResolver},
            builtinTypes,
            NotNull{&iceHandler},
            environmentScope
                ? environmentScope
                : globals.globalScope,
            globals.globalTypeFunctionScope,
            std::move(prepareModuleScopeWrap),
            nullptr,
            NotNull{cgData[i].dfg.get()},
            moduleInfo.requireCycles,
            cgraph.get(),
            nullptr
        };

        ConstraintSet cgResult =
            cg.run(sourceModule.root);

        module->constraintGenerationDidNotComplete =
            cg.recursionLimitMet;

        cgData[i].cgScopes =
            std::move(cg.scopes);

        for (ConstraintPtr& constraint :
             cgResult.constraints)
        {
            mergedConstraints.push_back(
                std::move(constraint)
            );
        }

        for (ConstraintPtr& deferred :
             cgResult.mergedDeferredConstraints)
        {
            mergedDeferredConstraints.push_back(
                std::move(deferred)
            );
        }

        mergedErrors.insert(
            mergedErrors.end(),
            std::make_move_iterator(
                cgResult.errors.begin()
            ),
            std::make_move_iterator(
                cgResult.errors.end()
            )
        );

        if (
            FFlag::LuauExportValueSyntax &&
            FFlag::LuauExportValueTypecheck
        )
        {
            module->scopes =
                cgData[i].cgScopes;

            synthesizeExportReturn(
                builtinTypes,
                NotNull{module.get()}
            );
        }

        TypePackId actualReturnType =
            cgData[i].cgScopes[0].second->returnType;

        ModulePtr placeholderModule =
            moduleResolver.getModule(
                moduleInfo.name
            );

        if (
            placeholderModule &&
            placeholderModule.get() != module.get()
        )
        {
            TypePackId placeholderPack =
                placeholderModule->returnType;

            auto placeholderHead =
                first(placeholderPack);

            std::optional<TypeId> actualHead;

            TypePack headPack =
                extendTypePack(
                    *scc->sharedArena,
                    builtinTypes,
                    actualReturnType,
                    1
                );

            if (!headPack.head.empty())
            {
                actualHead =
                    headPack.head[0];
            }

            if (
                placeholderHead &&
                actualHead &&
                get<BlockedType>(*placeholderHead)
            )
            {
                emplaceType<BoundType>(
                    asMutable(*placeholderHead),
                    *actualHead
                );
            }

            placeholderModule->exportedTypeBindings =
                cgData[i]
                    .cgScopes[0]
                    .second
                    ->exportedTypeBindings;
        }

        moduleInfo.module =
            std::move(module);
    }

    LUAU_ASSERT(
        !cgData.empty() &&
        !cgData[0].cgScopes.empty()
    );

    ScopePtr rootScope =
        cgData[0].cgScopes[0].second;

    NotNull<Scope> rootScopeNotNull{
        rootScope.get()
    };

    ConstraintSet constraintSet{
        rootScopeNotNull,
        std::move(mergedConstraints),
        std::move(mergedDeferredConstraints),
        TypeIds{},
        DenseHashMap<Scope*, TypeId>{nullptr},
        std::vector<TypeError>{},
    };

    Subtyping subtyping{
        builtinTypes,
        NotNull{scc->sharedArena.get()},
        NotNull{&normalizer},
        NotNull{&typeFunctionRuntime},
        NotNull{&iceHandler}
    };

    ConstraintSolver cs{
        NotNull{&normalizer},
        NotNull{&typeFunctionRuntime},
        item.modules[0].module,
        NotNull<ModuleResolver>{&moduleResolver},
        {},
        nullptr,
        NotNull<const DataFlowGraph>{
            cgData[0].dfg.get()
        },
        typeCheckLimits,
        std::move(constraintSet),
        cgraph.get(),
        NotNull{&subtyping}
    };

    try
    {
        cs.run();
    }
    catch (const TimeLimitError&)
    {
        for (BuildQueueModuleInfo& moduleInfo :
             item.modules)
        {
            moduleInfo.module->timeout = true;
        }
    }
    catch (const UserCancelError&)
    {
        for (BuildQueueModuleInfo& moduleInfo :
             item.modules)
        {
            moduleInfo.module->cancelled = true;
        }
    }

    {
        DenseHashMap<ModuleName, ModulePtr> nameToModule{
            nullptr
        };

        for (const BuildQueueModuleInfo& moduleInfo :
             item.modules)
        {
            nameToModule[moduleInfo.name] =
                moduleInfo.module;
        }

        for (TypeError& err : mergedErrors)
        {
            if (ModulePtr* modulePtr =
                    nameToModule.find(err.moduleName))
            {
                (*modulePtr)->errors.emplace_back(
                    std::move(err)
                );
            }
        }

        for (TypeError& err : cs.errors)
        {
            if (ModulePtr* modulePtr =
                    nameToModule.find(err.moduleName))
            {
                (*modulePtr)->errors.emplace_back(
                    std::move(err)
                );
            }
        }
    }

    for (size_t i = 0;
         i < item.modules.size();
         i++)
    {
        BuildQueueModuleInfo& moduleInfo =
            item.modules[i];

        ModulePtr module =
            moduleInfo.module;

        const SourceModule& sourceModule =
            *moduleInfo.sourceModule;

        module->scopes =
            std::move(cgData[i].cgScopes);

        module->type =
            sourceModule.type;

        if (module->timeout || module->cancelled)
        {
            ScopePtr moduleScope =
                module->getModuleScope();

            moduleScope->returnType =
                builtinTypes->errorTypePack;

            for (auto& [name, ty] :
                 module->declaredGlobals)
            {
                ty =
                    builtinTypes->errorType;
            }

            for (auto& [name, tf] :
                 module->exportedTypeBindings)
            {
                tf.type =
                    builtinTypes->errorType;
            }
        }
        else
        {
            try
            {
                Mode mode =
                    module->mode;

                switch (mode)
                {
                case Mode::Nonstrict:
                    Luau::checkNonStrict(
                        builtinTypes,
                        NotNull{&typeFunctionRuntime},
                        NotNull{&iceHandler},
                        NotNull{&unifierState},
                        NotNull{cgData[i].dfg.get()},
                        NotNull{&typeCheckLimits},
                        sourceModule,
                        module.get()
                    );
                    break;

                case Mode::Definition:
                case Mode::Strict:
                    Luau::check(
                        builtinTypes,
                        NotNull{&typeFunctionRuntime},
                        NotNull{&unifierState},
                        NotNull{&typeCheckLimits},
                        nullptr,
                        sourceModule,
                        module.get()
                    );
                    break;

                case Mode::NoCheck:
                    break;
                }
            }
            catch (const TimeLimitError&)
            {
                module->timeout = true;
            }
            catch (const UserCancelError&)
            {
                module->cancelled = true;
            }
        }

        unfreeze(module->interfaceTypes);

        module->clonePublicInterface(
            builtinTypes,
            iceHandler,
            SolverMode::New
        );

        if (module->mode == Mode::NoCheck)
        {
            module->errors.clear();
            continue;
        }

        ErrorVec parseErrors;

        for (const ParseError& pe :
             sourceModule.parseErrors)
        {
            parseErrors.emplace_back(
                pe.getLocation(),
                moduleInfo.name,
                SyntaxError{pe.what()}
            );
        }

        module->errors.insert(
            module->errors.begin(),
            parseErrors.begin(),
            parseErrors.end()
        );
    }

    freeze(*scc->sharedArena);

    for (BuildQueueModuleInfo& moduleInfo :
         item.modules)
    {
        freeze(
            moduleInfo.module->interfaceTypes
        );
    }

    if (FFlag::LuauCyclicRequireTopLevelAccessError)
    {
        bool hasRuntimeCycle = false;

        for (const BuildQueueModuleInfo& moduleInfo :
             item.modules)
        {
            if (!moduleInfo.requireCycles.empty())
            {
                hasRuntimeCycle = true;
                break;
            }
        }

        if (hasRuntimeCycle)
        {
            for (BuildQueueModuleInfo& moduleInfo :
                 item.modules)
            {
                errorOnCyclicTopLevelAccess(
                    *moduleInfo.sourceModule,
                    moduleInfo.module,
                    scc->members
                );
            }
        }
    }
}

void Frontend::checkBuildQueueItem(BuildQueueItem& item)
{
    if (FFlag::LuauCyclicRequireTypeInference && item.scc && (item.modules.size() == item.scc->members.size()))
    {
        checkSCCBuildQueueItem(item);

        return;
    }

    BuildQueueModuleInfo& moduleInfo = item.modules[0];

    SourceNode& sourceNode = *moduleInfo.sourceNode;

    const SourceModule& sourceModule = *moduleInfo.sourceModule;

    const Config& config = moduleInfo.config;

    Mode mode;

    if (FFlag::DebugLuauForceStrictMode)
    {
        mode = Mode::Strict;
    }
    else if (FFlag::DebugLuauForceNonStrictMode)
    {
        mode = Mode::Nonstrict;
    }
    else
    {
        mode = sourceModule.mode.value_or(config.mode);
    }

    moduleInfo.sourceModule->mode = {mode};

    ScopePtr environmentScope = moduleInfo.environmentScope;

    double timestamp = getTimestamp();

    const std::vector<RequireCycle>& requireCycles = moduleInfo.requireCycles;

    TypeCheckLimits typeCheckLimits = makeTypeCheckLimits(item.options);

    if (item.options.applyInternalLimitScaling)
    {
        if (FInt::LuauTarjanChildLimit > 0)
        {
            typeCheckLimits.instantiationChildLimit = std::max(1, int(FInt::LuauTarjanChildLimit * sourceNode.autocompleteLimitsMult));
        }
        else
        {
            typeCheckLimits.instantiationChildLimit = std::nullopt;
        }

        if (FInt::LuauTypeInferIterationLimit > 0)
        {
            typeCheckLimits.unifierIterationLimit = std::max(1, int(FInt::LuauTypeInferIterationLimit * sourceNode.autocompleteLimitsMult));
        }
        else
        {
            typeCheckLimits.unifierIterationLimit = std::nullopt;
        }
    }

    if (item.options.forAutocomplete)
    {
        ModulePtr moduleForAutocomplete =
            check(sourceModule, Mode::Strict, requireCycles, environmentScope, true, false, moduleInfo.stats, std::move(typeCheckLimits));

        double duration = getTimestamp() - timestamp;

        moduleForAutocomplete->checkDurationSec = duration;

        if (item.options.moduleTimeLimitSec && item.options.applyInternalLimitScaling)
        {
            applyInternalLimitScaling(sourceNode, moduleForAutocomplete, *item.options.moduleTimeLimitSec);
        }

        moduleInfo.stats.timeCheck += duration;

        moduleInfo.stats.filesStrict += 1;

        if (item.options.collectTypeAllocationStats)
        {
            moduleInfo.stats.typesAllocated += moduleForAutocomplete->internalTypes.types.size();

            moduleInfo.stats.typePacksAllocated += moduleForAutocomplete->internalTypes.typePacks.size();

            moduleInfo.stats.boolSingletonsMinted += moduleForAutocomplete->internalTypes.boolSingletonsMinted;

            moduleInfo.stats.strSingletonsMinted += moduleForAutocomplete->internalTypes.strSingletonsMinted;

            moduleInfo.stats.uniqueStrSingletonsMinted += moduleForAutocomplete->internalTypes.uniqueStrSingletonsMinted.size();
        }

        if (item.options.customModuleCheck)
        {
            item.options.customModuleCheck(sourceModule, *moduleForAutocomplete);
        }

        moduleInfo.module = moduleForAutocomplete;

        return;
    }

    ModulePtr module =
        check(sourceModule, mode, requireCycles, environmentScope, false, item.recordJsonLog, moduleInfo.stats, std::move(typeCheckLimits));

    double duration = getTimestamp() - timestamp;

    module->checkDurationSec = duration;

    if (item.options.moduleTimeLimitSec && item.options.applyInternalLimitScaling)
    {
        applyInternalLimitScaling(sourceNode, module, *item.options.moduleTimeLimitSec);
    }

    moduleInfo.stats.timeCheck += duration;

    moduleInfo.stats.filesStrict += (mode == Mode::Strict) ? 1 : 0;

    moduleInfo.stats.filesNonstrict += (mode == Mode::Nonstrict) ? 1 : 0;

    if (item.options.collectTypeAllocationStats)
    {
        moduleInfo.stats.typesAllocated += module->internalTypes.types.size();

        moduleInfo.stats.typePacksAllocated += module->internalTypes.typePacks.size();

        moduleInfo.stats.boolSingletonsMinted += module->internalTypes.boolSingletonsMinted;

        moduleInfo.stats.strSingletonsMinted += module->internalTypes.strSingletonsMinted;

        moduleInfo.stats.uniqueStrSingletonsMinted += module->internalTypes.uniqueStrSingletonsMinted.size();
    }

    if (item.options.customModuleCheck)
    {
        item.options.customModuleCheck(sourceModule, *module);
    }

    if (getLuauSolverMode() == SolverMode::New && mode == Mode::NoCheck)
    {
        module->errors.clear();
    }

    if (item.options.runLintChecks)
    {
        LUAU_TIMETRACE_SCOPE("lint", "Frontend");

        LintOptions lintOptions = item.options.enabledLintWarnings.value_or(config.enabledLint);

        filterLintOptions(lintOptions, sourceModule.hotcomments, mode);

        double lintTimestamp = getTimestamp();

        std::vector<LintWarning> warnings =
            Luau::lint(sourceModule.root, *sourceModule.names, environmentScope, module.get(), sourceModule.hotcomments, lintOptions);

        moduleInfo.stats.timeLint += getTimestamp() - lintTimestamp;

        module->lintResult = classifyLints(warnings, config);
    }

    if (!item.options.retainFullTypeGraphs)
    {
        unfreeze(module->interfaceTypes);

        copyErrors(module->errors, module->interfaceTypes, builtinTypes);

        freeze(module->interfaceTypes);

        module->internalTypes.clear();

        module->defArena.allocator.clear();

        module->keyArena.allocator.clear();
    }

    moduleInfo.module = std::move(module);
}

void Frontend::checkBuildQueueItems(std::vector<BuildQueueItem>& items)
{
    for (BuildQueueItem& item : items)
    {
        checkBuildQueueItem(item);
    }
}

void Frontend::recordItemResult(const BuildQueueItem& item)
{
    if (item.exception)
    {
        std::rethrow_exception(item.exception);
    }

    auto recordModuleInfo = [&](const BuildQueueModuleInfo& moduleInfo)
    {
        bool replacedModule = false;

        if (item.options.forAutocomplete)
        {
            replacedModule = moduleResolverForAutocomplete.setModule(moduleInfo.name, moduleInfo.module);

            moduleInfo.sourceNode->dirtyModuleForAutocomplete = false;
        }
        else
        {
            replacedModule = moduleResolver.setModule(moduleInfo.name, moduleInfo.module);

            moduleInfo.sourceNode->dirtyModule = false;
        }

        if (replacedModule)
        {
            LUAU_TIMETRACE_SCOPE("Frontend::invalidateDependentModules", "Frontend");

            LUAU_TIMETRACE_ARGUMENT("name", moduleInfo.name.c_str());

            traverseDependents(
                moduleInfo.name,
                [forAutocomplete = item.options.forAutocomplete](SourceNode& sourceNode)
                {
                    bool traverseSubtree = !sourceNode.hasInvalidModuleDependency(forAutocomplete);

                    sourceNode.setInvalidModuleDependency(true, forAutocomplete);

                    return traverseSubtree;
                }
            );
        }

        moduleInfo.sourceNode->setInvalidModuleDependency(false, item.options.forAutocomplete);

        stats.timeCheck += moduleInfo.stats.timeCheck;

        stats.timeLint += moduleInfo.stats.timeLint;

        stats.filesStrict += moduleInfo.stats.filesStrict;

        stats.filesNonstrict += moduleInfo.stats.filesNonstrict;

        if (item.options.collectTypeAllocationStats)
        {
            stats.typesAllocated += moduleInfo.stats.typesAllocated;

            stats.typePacksAllocated += moduleInfo.stats.typePacksAllocated;

            stats.boolSingletonsMinted += moduleInfo.stats.boolSingletonsMinted;

            stats.strSingletonsMinted += moduleInfo.stats.strSingletonsMinted;

            stats.uniqueStrSingletonsMinted += moduleInfo.stats.uniqueStrSingletonsMinted;
        }

        stats.dynamicConstraintsCreated += moduleInfo.stats.dynamicConstraintsCreated;
    };

    if (FFlag::LuauCyclicRequireTypeInference)
    {
        for (const BuildQueueModuleInfo& moduleInfo : item.modules)
        {
            recordModuleInfo(moduleInfo);
        }
    }
    else
    {
        recordModuleInfo(item.modules[0]);
    }
}

void Frontend::performQueueItemTask(std::shared_ptr<BuildQueueWorkState> state, size_t itemPos)
{
    BuildQueueItem& item = state->buildQueueItems[itemPos];

    try
    {
        checkBuildQueueItem(item);
    }
    catch (const Luau::InternalCompilerError&)
    {
        item.exception = std::current_exception();
    }

    {
        std::unique_lock guard(state->mtx);

        state->readyQueueItems.push_back(itemPos);
    }

    state->cv.notify_one();
}

void Frontend::sendQueueItemTasks(std::shared_ptr<BuildQueueWorkState> state, const std::vector<size_t>& items)
{
    std::vector<std::function<void()>> tasks;

    tasks.reserve(items.size());

    for (size_t itemPos : items)
    {
        BuildQueueItem& item = state->buildQueueItems[itemPos];

        LUAU_ASSERT(!item.processing);

        item.processing = true;

        tasks.emplace_back(
            [this, state, itemPos]()
            {
                performQueueItemTask(state, itemPos);
            }
        );
    }

    state->processing += items.size();

    state->executeTasks(std::move(tasks));
}

void Frontend::sendQueueCycleItemTask(std::shared_ptr<BuildQueueWorkState> state)
{
    for (size_t i = 0; i < state->buildQueueItems.size(); i++)
    {
        BuildQueueItem& item = state->buildQueueItems[i];

        if (item.processing)
            continue;

        item.processing = true;

        state->processing++;

        state->executeTasks({[this, state, i]()
                             {
                                 performQueueItemTask(state, i);
                             }});

        return;
    }
}

ScopePtr Frontend::getModuleEnvironment(const SourceModule& module, const Config& config, bool forAutocomplete) const
{
    ScopePtr result;

    if (forAutocomplete)
        result = globalsForAutocomplete.globalScope;
    else
        result = globals.globalScope;

    if (module.environmentName)
        result = getEnvironmentScope(*module.environmentName);

    if (!config.globals.empty())
    {
        result = std::make_shared<Scope>(result);

        for (const std::string& global : config.globals)
        {
            AstName name = module.names->get(global.c_str());

            if (name.value)
                result->bindings[name].typeId = builtinTypes->anyType;
        }
    }

    return result;
}

LintResult Frontend::classifyLints(const std::vector<LintWarning>& warnings, const Config& config)
{
    LintResult result;

    for (const auto& w : warnings)
    {
        if (config.lintErrors || config.fatalLint.isEnabled(w.code))
            result.errors.push_back(w);
        else
            result.warnings.push_back(w);
    }

    return result;
}

TypeId Frontend::parseType(
    NotNull<Allocator> allocator,
    NotNull<AstNameTable> nameTable,
    NotNull<InternalErrorReporter> iceHandler,
    TypeCheckLimits limits,
    NotNull<TypeArena> arena,
    std::string_view source
)
{
    ParseNodeResult<AstType> parseResult = Parser::parseType(
        source.data(),
        source.size(),
        *nameTable,
        *allocator
    );

    if (!parseResult.root)
        iceHandler->ice("Frontend::parseType was given an unparseable type");

    if (!parseResult.errors.empty())
        iceHandler->ice("Frontend::parseType error: " + parseResult.errors.front().getMessage());

    ModulePtr module = std::make_shared<Module>();

    UnifierSharedState unifierState{iceHandler};
    unifierState.counters.recursionLimit = FInt::LuauTypeInferRecursionLimit;
    unifierState.counters.iterationLimit =
        limits.unifierIterationLimit.value_or(FInt::LuauTypeInferIterationLimit);

    Normalizer normalizer{
        arena,
        builtinTypes,
        NotNull{&unifierState},
        SolverMode::New
    };

    TypeFunctionRuntime typeFunctionRuntime{
        iceHandler,
        NotNull{&limits}
    };
    typeFunctionRuntime.allowEvaluation = true;

    NullModuleResolver moduleResolver;

    DataFlowGraph dfg = DataFlowGraphBuilder::empty(
        NotNull{&module->defArena},
        NotNull{&module->keyArena}
    );

    ConstraintGenerator cg{
        module,
        NotNull{&normalizer},
        NotNull{&typeFunctionRuntime},
        NotNull{&moduleResolver},
        builtinTypes,
        iceHandler,
        globals.globalScope,
        globals.globalScope,
        nullptr,
        nullptr,
        NotNull{&dfg},
        {},
        nullptr
    };

    TypeId t = cg.resolveType(
        globals.globalScope,
        parseResult.root,
        false
    );

    if (!cg.constraints.empty())
        iceHandler->ice("Not yet implemented: parseType cannot reduce other type aliases");

    return t;
}

} // namespace Luau