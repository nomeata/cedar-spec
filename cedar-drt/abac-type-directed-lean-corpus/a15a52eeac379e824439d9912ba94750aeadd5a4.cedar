forbid(
  principal == a::"\0\0\0\0",
  action in [Action::"action"],
  resource
) when {
  ((true && (Action::"action" is a)) && (Action::"action" in Action::"action")) && (Action::"action" in a::"\0\0\u{1f}\0")
};
