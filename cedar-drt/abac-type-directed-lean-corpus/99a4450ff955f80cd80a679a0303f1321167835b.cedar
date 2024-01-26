@B("")
@r("")
@r333333203303("")
forbid(
  principal == a::"\0\t\063\u{1}\0\0\t",
  action == Action::"action",
  resource == a::"\0\t\063\u{1}\0\0\t"
) when {
  true && (if (if (resource is a) then (if true then true else true) else (if true then true else true)) then (if (if true then true else true) then (if false then true else true) else (if true then true else true)) else (if (if true then false else false) then false else false))
};
