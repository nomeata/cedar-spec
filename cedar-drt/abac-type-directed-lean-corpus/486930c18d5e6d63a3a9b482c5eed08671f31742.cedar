permit(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::"\0\0\0\0\0\0\0\0"
) when {
  true && (((ip(">")).isIpv4()) && false)
};
