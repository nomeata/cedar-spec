permit(
  principal is a in a::"\n\n\n\n\n\n\n\n\n",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ((ip(principal["P"])).isIpv4())) && ((ip(principal["P"])).isIpv4())
};
