permit(
  principal is a in a::"jjj",
  action in [Action::"action"],
  resource == a::"jjj"
) when {
  (true && ((Action::"action" in context) is a)) && principal
};
