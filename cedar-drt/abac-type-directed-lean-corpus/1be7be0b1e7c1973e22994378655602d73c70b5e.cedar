forbid(
  principal == a::"63333330",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((decimal("0.1")) == (decimal("0.1"))) then (if true then (-1) else (-1)) else (if false then (-1) else (-1))) == (if ((decimal("0.1")) == (-1)) then (-1) else (if false then (-1) else (-1))))) && ((if ((ip("3333:3276:3333:ca33:aa36:36ff:3636:ff36/50")).isInRange(ip("3276:fd98:ff00:ffff:26e:6e6e:6e6e:6e33/51"))) then (if false then (ip("48.6.54.0")) else (ip("110.110.110.0"))) else (ip("233666633333"))).isIpv4())) && (a::"" in resource)
};
