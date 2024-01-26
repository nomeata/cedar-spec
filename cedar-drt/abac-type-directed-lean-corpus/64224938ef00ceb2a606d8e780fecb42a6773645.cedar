forbid(
  principal == a::"6\u{1}\u{1}zef\00",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("255.255.255.253/2\u{12}")).isLoopback()) then [] else []) == [])) && true) && true
};
