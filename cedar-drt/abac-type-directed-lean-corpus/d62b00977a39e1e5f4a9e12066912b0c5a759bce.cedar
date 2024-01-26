permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  (true && ((ip("\0$&\0\0\0\t")).isIpv4())) && false
};
