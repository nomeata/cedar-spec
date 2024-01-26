@Bssssssssssjsss("6")
permit(
  principal is a in a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
  action in [Action::"action"],
  resource == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
) when {
  true && ((ip(principal["Bsss"])).isIpv4())
};
