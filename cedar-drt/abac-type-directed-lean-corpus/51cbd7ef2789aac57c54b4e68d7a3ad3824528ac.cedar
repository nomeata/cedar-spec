permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::"\0\0\0"
) when {
  (true && ((if ((ip("43.54.160.54")).isIpv4()) then (ip("")) else (ip(""))).isMulticast())) && false
};
