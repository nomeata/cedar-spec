forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"j\0\0\0"
) when {
  false
};
