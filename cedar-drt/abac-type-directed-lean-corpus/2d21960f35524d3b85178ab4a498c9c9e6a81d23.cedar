permit(
  principal,
  action == Action::"action",
  resource in a::"666>6666"
) when {
  (true && (resource is a)) && (Action::"action" is a)
};
