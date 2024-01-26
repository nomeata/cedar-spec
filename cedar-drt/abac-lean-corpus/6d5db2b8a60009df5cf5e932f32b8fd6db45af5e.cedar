forbid(
  principal,
  action in [Action::""],
  resource
) when {
  (true && principal) && false
};
