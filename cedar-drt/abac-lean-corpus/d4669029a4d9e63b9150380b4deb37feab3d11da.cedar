forbid(
  principal,
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (true.containsAll(a::""))) && false
};
