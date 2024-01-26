permit(
  principal == a::"C\0\0\0`\0",
  action in [Action::"action"],
  resource == a::"C\0\0\0`\0"
) when {
  true
};
