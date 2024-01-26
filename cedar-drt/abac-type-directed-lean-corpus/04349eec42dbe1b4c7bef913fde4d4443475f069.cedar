@kaa("$$")
permit(
  principal is r::Bss20ssss::m::a,
  action in [r::Bss20ssss::m::Action::"action"],
  resource
) when {
  ((true && (r::Bss20ssss::m::a::"\u{10}666667" is r::Bss20ssss::m::a)) && ((ip(principal["A"])).isIpv4())) && false
};
