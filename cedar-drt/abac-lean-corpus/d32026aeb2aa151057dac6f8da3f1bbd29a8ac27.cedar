forbid(
  principal == a::"\u{10}",
  action in [Action::"action"],
  resource
) when {
  true && ((a::"" == action) || false)
};
