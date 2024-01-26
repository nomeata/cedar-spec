permit(
  principal,
  action in [Action::"action"],
  resource == a::"j\0\u{10}"
) when {
  false && Action::"action"
};
