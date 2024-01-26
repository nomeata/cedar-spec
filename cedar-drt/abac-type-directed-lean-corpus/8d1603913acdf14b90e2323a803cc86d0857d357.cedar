permit(
  principal is a in a::"66666\u{1}",
  action in [Action::"action"],
  resource == a::"66666\u{1}"
) when {
  false
};
