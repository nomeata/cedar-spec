forbid(
  principal is a in a::"66id\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0$\0",
  action in [Action::"action"],
  resource
) when {
  true && (action has "")
};
