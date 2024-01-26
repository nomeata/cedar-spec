permit(
  principal is A002 in l::"",
  action == Action::"action",
  resource is A002 in m::""
) when {
  (true && ((ip(resource["A"])).isIpv4())) && ((ip(action["A"])).isIpv4())
};
