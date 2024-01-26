@r("po66")
permit(
  principal == a::"\0\0\0\0Y6\0\0\066",
  action == Action::"action",
  resource == a::"\0\0\0\0Y6\0\0\066"
) when {
  true && (!((ip("666666\0\0\0\0")).isIpv4()))
};
