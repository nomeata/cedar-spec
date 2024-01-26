forbid(
  principal is a in a::"\u{11}\u{1}\0\0\0\0\0\0\u{10}",
  action == Action::"action",
  resource is a in a::"\u{11}\u{1}\0\0\0\0\0\0\u{10}"
) when {
  false
};
