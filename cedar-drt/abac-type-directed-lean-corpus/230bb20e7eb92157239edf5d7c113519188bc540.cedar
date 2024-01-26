forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (([[]].containsAny([true])) || true)) && true
};
