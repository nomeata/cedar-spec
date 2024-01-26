permit(
  principal == a::"\0&o",
  action,
  resource == a::"\0&o"
) when {
  (true && ((ip("")).isIpv4())) && false
};
