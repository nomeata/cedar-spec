forbid(
  principal in a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  (true && ([if false then [] else [], if false then [] else [], [ip("112.122.255.54"), ip("::66:2000:66")]].containsAny([]))) && false
};
