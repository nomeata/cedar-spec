forbid(
  principal,
  action in [A::Action::"action"],
  resource is A::a in A::a::""
) when {
  (true && (A::a::"" in principal)) && ((if (!((-2531906049332683556) <= 7594034795847352540)) then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("0.0.0.0")) else (ip("0.0.0.0")))).isIpv6())
};
