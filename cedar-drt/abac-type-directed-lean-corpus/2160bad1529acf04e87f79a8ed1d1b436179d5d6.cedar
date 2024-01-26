forbid(
  principal == a::"\0\0\0\0\0\0\0\u{11}",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[ip("c3c3:c300::5cc3:c3c3:c3c3/66"), ip("54.54.54.54"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")], [ip("fd00::dcc3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:3434:3931:7f00:0/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:6767:6767:6767/66")], if false then [] else []] == [[ip("195.195.1955.195/30"), ip("bec3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")], [ip("c3c3:c3c3:c300::c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3::c3:c3c3:c3c3:c3c3/66")]])) && true) && ([ip("66666\u{16}6)666666["), ip("")].containsAny([]))
};
