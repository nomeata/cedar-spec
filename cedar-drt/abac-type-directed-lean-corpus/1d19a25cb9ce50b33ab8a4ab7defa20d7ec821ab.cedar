forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (principal == action)) && false) && false
};
