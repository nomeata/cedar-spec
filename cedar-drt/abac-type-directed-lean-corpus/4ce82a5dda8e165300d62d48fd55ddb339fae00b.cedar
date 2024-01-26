permit(
  principal == r::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("c3c3:c3c3:c300::c3c3:c3c3:c3c3/66")) == (ip("6133:3333:3133:3333:3333:efff:ffff:ffff/0"))) then (if true then (ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")) else (ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"))) else (if true then (ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")) else (ip("ffff:ffff:ffff:ffff:ffff:ffff:ff11:1119/126")))) == (if ((decimal("0.1")) == (decimal("123004564822556.6719"))) then (ip("")) else (if true then (ip("ffff:ff27:ffff:ffff:ffff:ffff:ffff:ffff/126")) else (ip("3535:3535:3535:3535:3535:3535:3535:3535/53")))))) && (r::"" is r)) && ((ip("")).isIpv4())
};
