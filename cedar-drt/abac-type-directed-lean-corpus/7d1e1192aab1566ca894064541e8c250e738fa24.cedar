forbid(
  principal is a in a::"6$\0~\0",
  action in [Action::"action"],
  resource
) when {
  true && (a::"" in action)
};
