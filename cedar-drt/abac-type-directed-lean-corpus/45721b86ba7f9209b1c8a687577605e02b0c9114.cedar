permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::"\0\0\0"
) when {
  (true && ((if ((ip("55.43.54.544//00")).isIpv4()) then (ip("111111@")) else (ip(""))).isMulticast())) && false
};
