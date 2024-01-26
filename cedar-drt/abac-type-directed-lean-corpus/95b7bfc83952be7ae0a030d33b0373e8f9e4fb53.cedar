permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  true && (!(action in a::"66"))
};
