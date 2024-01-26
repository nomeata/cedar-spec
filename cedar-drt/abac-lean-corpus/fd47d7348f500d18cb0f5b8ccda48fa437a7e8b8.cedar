forbid(
  principal is a,
  action in [Action::"action"],
  resource == a::"G\0\0\0\0\0"
) when {
  true
};
