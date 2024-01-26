forbid(
  principal == a::"\u{2}\0\0\0\0\0\0\0",
  action in [],
  resource is a in a::"\u{2}\0\0\0\0\0\0\0"
) when {
  true
};
