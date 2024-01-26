forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((a::"" == action) || (!(!a::"\u{10}")))
};
