permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::"63$\0"
) when {
  true && ((if ((ip("54.54.89.89")).isMulticast()) then (ip("")) else (ip(""))).isIpv4())
};
