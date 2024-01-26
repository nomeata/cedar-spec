forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[ip("c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("0:c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3")], [ip("::c3c3:c334:3439:317f:0:c3"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c300::c3c3:c3c3:c3c3:c3c3/66")], [ip("c3c3:c3c3:c3c3:c3c3:c3c3:3931:7f00:0/66"), ip("c3c3:c3c3:c3c3:c3c3:3636:3636:3636:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")]] == [[ip("c3c3:c3c3:c3c3:3931:7f00:0:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:6767:6767:6767/58"), ip("1:0:3636:36d3:cc36:ffff:ff33:3333")], [ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("3636:36c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3")], [ip("c300::c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("::c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")]])) && (true == ([ip("0.0.0.0/30"), ip("c3c3:c3c3:c3c3:c3c3:c336:3636:3636:36c3/66"), ip("c3c3:c3c3::1c3/66")].containsAny([ip("dada:c3c3:c3c3:c300::c3c3:c3c3"), ip("0.0.0.0"), ip("0.0.0.0")])))) && false
};
