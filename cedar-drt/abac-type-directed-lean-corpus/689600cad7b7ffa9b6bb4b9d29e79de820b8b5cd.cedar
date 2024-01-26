forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[ip("c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("0:c0c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3")], [ip("48.127.0.0/22"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3::c3:c3c3:c3c3/66")], [ip("49.127.0.0/30"), ip("c3c3:c3c3:c3c3:bec3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3be:c3c3:c3c3:c3c3:c300:0:c3/66")]] == [[ip("c3c3:c3c3::c3:c3c3:c3c3:c3c3/66"), ip("195.195.195.195/30"), ip("7f00:0:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3")], [ip("195.195.195.195/30"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/103"), ip("52.57.49.127")], [ip("dada:da36:3636::1:c3c3"), ip("0.0.0.0"), ip("0.0.0.0")]])) && false) && false
};
