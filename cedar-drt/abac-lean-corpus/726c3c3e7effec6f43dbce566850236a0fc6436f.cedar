forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((a::"\u{10}" == resource) || ((action == false) || action))
};
