@KAAtssssspp("337")
permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::"\n\n\n\n\n\n\n\u{e}\u{8}\n\n\n\n\n\n\n\u{1}\0\0\0e"
) when {
  (true && ((ip(principal["P"])).isIpv4())) && ((ip(principal["P"])).isIpv4())
};
