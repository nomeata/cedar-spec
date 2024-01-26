permit(
  principal,
  action == Action::"action",
  resource in a::"\0\u{4}\0"
) when {
  true
};
