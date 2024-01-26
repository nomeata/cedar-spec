forbid(
  principal == a::"j\0\0\0\0",
  action in [],
  resource
) when {
  true && ((![]) == (principal == principal))
};
