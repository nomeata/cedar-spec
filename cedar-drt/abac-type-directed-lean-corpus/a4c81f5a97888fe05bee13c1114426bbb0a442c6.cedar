permit(
  principal,
  action in [Action::"action"],
  resource == a::"\0\0\0\0"
) when {
  (true && (Action::"action" in Action::"action")) && (Action::"action" in action)
};
