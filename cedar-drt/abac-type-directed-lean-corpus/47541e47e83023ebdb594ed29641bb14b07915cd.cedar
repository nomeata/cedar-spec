forbid(
  principal,
  action in [A::Action::"action"],
  resource is A::a in A::a::""
) when {
  (true && (A::a::"" in principal)) && ((if (!((-2531906049332683556) <= 7593930990782775516)) then (ip("")) else (ip(""))).isIpv6())
};
