permit(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::"61"
) when {
  true && (((ip(">6666\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0A\0\0 \0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0")).isIpv4()) && (action has "6|6661"))
};
