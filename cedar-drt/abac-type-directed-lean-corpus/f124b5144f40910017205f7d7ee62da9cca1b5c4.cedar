permit(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::"C\0\0\0\0\0\0\0pr\0\0\0\0\0\0\0\0\0\0"
) when {
  true && (((ip(">6666>6\0")).isIpv4()) && (action has "6|6661"))
};
