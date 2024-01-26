forbid(
  principal in a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  (true && ([if false then [] else [], if false then [] else [], [ip("48.122.255.54"), ip("255255.102.101/24")]].containsAny([]))) && false
};
