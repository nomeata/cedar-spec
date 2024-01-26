permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ((ip("::36:c7c9:d9c9:ccc9")).isInRange(ip("0.0.0.0")))) && false
};
