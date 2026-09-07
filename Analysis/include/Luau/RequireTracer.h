// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details
#pragma once

#include "Luau/DenseHash.h"
#include "Luau/FileResolver.h"
#include "Luau/Location.h"

#include <string>
#include <vector>

namespace Luau
{

class AstNode;
class AstStatBlock;

struct RequireTraceResult
{
    DenseHashMap<const AstNode*, ModuleInfo> exprs;

    // Runtime module dependencies.
    std::vector<std::pair<ModuleName, Location>> requireList;

    // Dependencies that only exist because of `typeof(...)`.
    std::vector<std::pair<ModuleName, Location>> typeRequireList;
};

RequireTraceResult traceRequires(FileResolver* fileResolver, AstStatBlock* root, const ModuleName& currentModuleName, const TypeCheckLimits& limits);

} // namespace Luau
