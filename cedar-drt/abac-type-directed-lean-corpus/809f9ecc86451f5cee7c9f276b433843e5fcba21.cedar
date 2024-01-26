permit(
  principal,
  action == Action::"action",
  resource == a::"\0\0\0\u{4}\06"
) when {
  false
};
