export type Gamemode = {
    Start: (self: Gamemode) -> (),
}

local Gamemode: Gamemode = {
    Start = function(self)
    end,
}

return Gamemode