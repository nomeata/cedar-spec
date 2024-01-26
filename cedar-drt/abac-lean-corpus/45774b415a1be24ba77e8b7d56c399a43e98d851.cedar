permit(
  principal == a::"jj&j",
  action in [Action::"action"],
  resource
) when {
  true && Action::"action"
};
