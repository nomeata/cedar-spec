forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::"\u{6}\0\0N\0"
) when {
  true && (principal in action)
};
