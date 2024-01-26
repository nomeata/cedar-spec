permit(
  principal is a,
  action in [Action::"action"],
  resource == a::"\0\0\0\0\0\0\0\u{10}\0[d"
) when {
  false && principal
};
