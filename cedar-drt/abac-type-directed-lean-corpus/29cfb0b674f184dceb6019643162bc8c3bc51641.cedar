permit(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((ip(principal["P"])).isIpv4())) && (action in action)
};
