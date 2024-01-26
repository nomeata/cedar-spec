permit(
  principal == a::"@&o",
  action,
  resource == a::"@&o"
) when {
  (true && ((ip("")).isIpv4())) && false
};
