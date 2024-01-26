forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (if true then true else true)) && true
};
