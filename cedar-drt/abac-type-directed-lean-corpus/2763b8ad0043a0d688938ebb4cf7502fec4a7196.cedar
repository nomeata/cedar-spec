@B("")
@r("")
forbid(
  principal == a::"ints",
  action == Action::"action",
  resource == a::"ints"
) when {
  true && (if (if (if true then true else true) then (if true then true else true) else (if true then false else true)) then (if (if true then true else true) then (if true then true else true) else true) else true)
};
