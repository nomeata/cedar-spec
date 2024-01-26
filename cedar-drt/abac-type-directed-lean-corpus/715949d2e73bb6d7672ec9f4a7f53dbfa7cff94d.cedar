forbid(
  principal in B::"\u{1}\0\0",
  action == Action::"action",
  resource
) when {
  true
};
