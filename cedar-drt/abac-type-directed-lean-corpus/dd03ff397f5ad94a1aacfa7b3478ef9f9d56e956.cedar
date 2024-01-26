forbid(
  principal == a::"6\0",
  action,
  resource is a in a::"6\0"
) when {
  true && (principal has "")
};
