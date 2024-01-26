forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  true && (a::"6$\0" in action)
};
