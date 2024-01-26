forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("c3c3:c34e:c3c3:c3be:c3c3:c3c3:c3c3:c3c3/66")) == (ip("c3c3:c3c3:c3c3:c3c3::23:c3c3/66"))) then (if true then (ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66")) else (ip("c3c3:c3c3:c3c3:c300::c3c3:c3c3/66"))) else (if true then (ip("c3c3:c3c3:c3c3:3434:3931:7f00:0:c3c3/66")) else (ip("fd00:36c3:c3c3:c306:0:67:c3c3:c3c3/0")))) == (if ((ip("c3c3:c3c3:c334:3439:317f:0:c3:c3c3/66")) == (ip("c3c3:ffff:ffff:ffff:ffff:ffff:ffff:ffff/66"))) then (ip("0.0.0.0")) else (ip("0.0.0.0"))))) && false) && false
};
