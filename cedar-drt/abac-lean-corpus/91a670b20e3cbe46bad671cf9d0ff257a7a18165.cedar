forbid(
  principal is a in a::"J",
  action in [Action::"action"],
  resource is a in a::"J"
) when {
  true && (!(context is a))
};
