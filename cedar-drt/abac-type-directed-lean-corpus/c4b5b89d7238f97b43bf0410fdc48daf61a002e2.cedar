permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::"\0\0\0"
) when {
  (true && ((if ((ip("55.43.54.54/00")).isIpv4()) then (ip("")) else (ip(""))).isMulticast())) && ([].containsAny([]))
};
