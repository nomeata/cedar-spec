forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ([[[], []], []].containsAny(if false then (if true then [] else []) else [true, true, true]))
};
