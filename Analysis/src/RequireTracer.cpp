// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details

#include "Luau/RequireTracer.h"

#include "Luau/Ast.h"

#include "Luau/Common.h"

#include "Luau/FileResolver.h"

namespace Luau

{

namespace

{

struct RequireCall
{
    AstExprCall* call;
    bool typeOnly;
};

struct RequireTracer : AstVisitor
{
    FileResolver* fileResolver;
    ModuleName currentModuleName;
    TypeCheckLimits limits;
    RequireTraceResult result;
    std::vector<RequireCall> requireCalls;
    bool insideTypeof = false;

    RequireTracer(
        FileResolver* fileResolver,
        ModuleName currentModuleName,
        TypeCheckLimits limits
    )
        : fileResolver(fileResolver)
        , currentModuleName(std::move(currentModuleName))
        , limits(limits)
    {
    }

    bool visit(AstExprCall* expr) override
    {
        if (expr->func)
        {
            if (AstExprGlobal* global =
                    expr->func->as<AstExprGlobal>())
            {
                if (
                    global->name == "require" &&
                    expr->args.size >= 1
                )
                {
                    requireCalls.push_back({
                        expr,
                        insideTypeof,
                    });
                }
            }
        }

        return true;
    }

    bool visit(AstTypeTypeof* node) override
    {
        bool previousInsideTypeof =
            insideTypeof;

        insideTypeof = true;

        node->expr->visit(this);

        insideTypeof =
            previousInsideTypeof;

        return false;
    }

    bool visit(AstExprConstantString* node) override
    {
        return true;
    }

    bool visit(AstExprGlobal* node) override
    {
        return true;
    }

    bool visit(AstExprIndexName* node) override
    {
        return true;
    }

    bool visit(AstExprIndexExpr* node) override
    {
        return true;
    }

    bool visit(AstExprLocal* node) override
    {
        return true;
    }
};

} // namespace

RequireTraceResult traceRequires(
    FileResolver* fileResolver,
    AstStatBlock* root,
    const ModuleName& currentModuleName,
    const TypeCheckLimits& limits
)
{
    RequireTracer tracer{
        fileResolver,
        currentModuleName,
        limits,
    };

    root->visit(&tracer);

    tracer.result.requireList.reserve(
        tracer.requireCalls.size()
    );

    tracer.result.typeRequireList.reserve(
        tracer.requireCalls.size()
    );

    for (const RequireCall& require :
         tracer.requireCalls)
    {
        AstExpr* arg =
            require.call->args.data[0];

        if (
            const ModuleInfo* info =
                tracer.result.exprs.find(arg)
        )
        {
            if (require.typeOnly)
            {
                tracer.result
                    .typeRequireList
                    .push_back({
                        info->name,
                        require.call->location,
                    });
            }
            else
            {
                tracer.result
                    .requireList
                    .push_back({
                        info->name,
                        require.call->location,
                    });
            }

            ModuleInfo infoCopy = *info;

            tracer.result.exprs[
                require.call
            ] = std::move(infoCopy);
        }
        else
        {
            tracer.result.exprs[
                require.call
            ] = {};
        }
    }

    return std::move(tracer.result);
}

} // namespace Luau