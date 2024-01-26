forbid(
  principal is a in a::"\u{1}/6",
  action in [Action::"action"],
  resource is a in a::"\u{1}/6"
) when {
  ((true && ((a::"\u{1}/6" is a) == (principal is a))) && (a::"\u{1}/6" in Action::"action")) && ((decimal("")).lessThanOrEqual(decimal("6")))
};
