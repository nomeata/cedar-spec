permit(
  principal in a::"\u{10}\0[d",
  action in [Action::"action"],
  resource
) when {
  ((true && [a::"\u{10}\0[d", a::"\u{10}\0[d", context, (!principal) is a]) && principal) && a::"\u{10}\0[d"
};
