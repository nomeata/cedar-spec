forbid(
  principal is a,
  action == Action::"action",
  resource == a::"2"
) when {
  false && (Action::"action" in action)
};
