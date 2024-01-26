permit(
  principal is a,
  action == Action::"action",
  resource == a::"m\0\0\0\0\0l"
) when {
  true && (action.lessThan(false, !(!principal), false))
};
