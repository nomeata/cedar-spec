permit(
  principal is a in a::"666666666666666666666666",
  action in [Action::"action"],
  resource is a in a::"666666666666666666666666"
) when {
  (true && ((ip(principal["Z"])).isIpv4())) && ((ip(action["Z"])).isIpv4())
};
