forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (if (if (if false then false else false) then true else true) then true else true)) && true
};
