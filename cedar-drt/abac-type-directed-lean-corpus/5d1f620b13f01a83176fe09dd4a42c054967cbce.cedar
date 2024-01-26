permit(
  principal in a::"4444",
  action == Action::"action",
  resource
) when {
  ((true && ((Action::"action" is a) == (Action::"action" is a))) && (a::"4444" is a)) && (action is a)
};
