forbid(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ([].contains((ip("\0\0\0")).isIpv4()))) && false
};
