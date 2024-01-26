forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[ip("c3c3:c300::5cc3:c3c3:c3c3/66"), ip("c3c3:c3c3:c336:a436:c2f2:f237:3732:3937/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:6767:6767:6767/66")], [ip("3434:3931:7f00:0:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:6767:6767:6767:6767:67c3:c3c3:c3c3/66"), ip("54.54.54.54")], [ip("c3c3:c339:317f:0:c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c367:6767:6767:6767:6767:c3c3/66"), ip("242.178.54.54")]] == [[ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3::c3:c3c3/66"), ip("c3c3:c3c3:600::1:c334:3439/66")], [ip("6767:6767:6767:6767:c3c3:c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3::c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")], [ip("c3c3:c3c3:fd00::c3c3:c3c3:c3c3/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:3434:3931/66"), ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")]])) && ((if ((ip("c3c3:c3c3:c3c3:c3c3:c3c3:3931:7f00:0/66")) == (ip("c3c3:bbc3:c3c3:c3c3:c3c3:c3c3:c3c3:6767/66"))) then (if true then (ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")) else (ip("c3c3:c3c3:c3c3:c3c3:c367:6767:6767:6767/66"))) else (if false then (ip("6767:6767:6767:6767:c3c3:c3c3:c300:c3/66")) else (ip("::1:c3c3:c3c3:c3c3:c3c3:c3c3")))) == (if ((ip("c3c3:c300::c3c3:c3c3:c3c3:c3c3/66")) == (ip("0.0.0.0"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))))) && false
};
