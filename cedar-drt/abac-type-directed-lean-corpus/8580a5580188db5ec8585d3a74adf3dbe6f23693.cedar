permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true && ([].contains(if ((ip("0..00.0.1")).isIpv4()) then 0 else 0))
};
