permit(
  principal == r::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("c3c3:c3c3:c300::c3c3:c3c3:c3c3/66")) == (ip("6133:3333:3133:3333:3333:efff:ffff:ffff/0"))) then (if true then (ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")) else (ip("1ff:97ff:5bff:ffff:ff:2ff:ff25:ffff"))) else (ip(""))) == (ip("::91:9191:9191:9191")))) && false) && false
};
