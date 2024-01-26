@r("\u{1}\0k")
forbid(
  principal,
  action in [Action::"ef"],
  resource
) when {
  ((true && (principal in context)) && true) && principal
};
