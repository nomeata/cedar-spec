forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("c3c3:c3c3:c3c3:c3be:c3c3:c3c3:c3c3:c3c3/66")) == (ip("ffff:ffff:ffff:ffff:ffff:ffe5:e523:c3/126"))) then (if true then (ip("dd11dd1::dd11dd44::dd11dd11::dd11dd11::d1d1:4141:4141:4141/80")) else (ip("dd1dd11::dd11dd11:d1d1:d1d4:d1d1:d1d1:d1d1:4141/80"))) else (if true then (ip("dd11d11::dd11dd11::dd1d44::dd11d1:d1d1:ff3b:ff12:ffff/80")) else (ip("::1c3:c3c3:c3ff:ffff:ffff:ffff")))) == (ip("0.0.0.0")))) && false) && false
};
