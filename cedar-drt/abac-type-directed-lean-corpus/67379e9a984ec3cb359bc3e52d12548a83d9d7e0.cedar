forbid(
  principal is a,
  action == Action::"action",
  resource in a::"67\u{1}\0\0\0                        "
) when {
  true
};
