@A33("")
@r("6")
forbid(
  principal == a::"\0\t\06",
  action == Action::"action",
  resource == a::"\0\t\06"
) when {
  true && (if (if (if true then true else true) then (if true then true else true) else (if true then true else true)) then (if (if true then true else true) then (if true then true else true) else (if true then false else false)) else false)
};
