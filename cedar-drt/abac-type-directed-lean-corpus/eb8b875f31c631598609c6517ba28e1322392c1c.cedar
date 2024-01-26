forbid(
  principal,
  action in [wIII::wI33::JscYYYY::wIII::Action::"action"],
  resource
) when {
  ((true && ((principal is wIII::wI33::JscYYYY::wIII::a) == ([action].contains(wIII::wI33::JscYYYY::wIII::Action::"action")))) && ((if ((ip("::b5:b536:3636:36b5")).isIpv6()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isIpv6())) && false
};
