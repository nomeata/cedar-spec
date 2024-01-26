permit(
  principal is a in a::"\n\n\n\n\n\n\n\u{e}\u{8}\n\n\n\n\n\u{17}\u{17}\u{17}\u{17}\u{17}\u{17}\u{17}*\u{17}\u{17}\u{17}\u{17}\u{17}\u{17}\u{17}\u{17}\u{17}\u{17}\n\u{17}\u{17}\n\u{17}\n\n\n\n\n\n\n\n\n",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ((ip(principal["P"])).isIpv4())) && ((ip(principal["P"])).isIpv4())
};
