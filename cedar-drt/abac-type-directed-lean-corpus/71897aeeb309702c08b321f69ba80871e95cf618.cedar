permit(
  principal is l in l::"",
  action in [Action::"\u{11}66"],
  resource is l in l::""
) when {
  (true && ((ip(principal["r"])).isIpv4())) && ((ip(principal["r"])).isIpv4())
};
