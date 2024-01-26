forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[ip("c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("0:c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3")], [ip("c3c3:c3c3:c3c3:c332:3739:307f:0:c3/66"), ip("c3c3:c3c3:c3c3:c367:6767:6767:6767:6767/66"), ip("54.194.242.242")], [ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c339/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/0"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c340:c3c3/66")]] == [[ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3ff:10c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")], if false then [] else [], if false then [] else []])) && ((ip("")).isIpv4())) && (resource is a)
};
