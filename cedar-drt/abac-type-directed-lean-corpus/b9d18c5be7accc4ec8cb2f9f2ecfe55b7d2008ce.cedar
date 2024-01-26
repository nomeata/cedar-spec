permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource == a::"YY\u{10}\0"
) when {
  false
};
