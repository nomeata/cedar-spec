permit(
  principal == a::"\0&o",
  action,
  resource == a::"\0&o"
) when {
  (true && ((ip("\0")).isIpv4())) && false
};
