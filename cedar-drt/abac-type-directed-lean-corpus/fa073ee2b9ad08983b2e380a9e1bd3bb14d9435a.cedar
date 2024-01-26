permit(
  principal == a::"",
  action,
  resource is a in a::""
) when {
  (true && ((ip("\06")).isIpv4())) && false
};
