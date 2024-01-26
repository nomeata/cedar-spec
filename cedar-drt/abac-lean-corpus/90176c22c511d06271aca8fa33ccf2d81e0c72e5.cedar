permit(
  principal is a,
  action == Action::"action",
  resource == a::"\0\0mpl"
) when {
  true && (false.lessThan("\u{3}\u{3}\u{3}"))
};
