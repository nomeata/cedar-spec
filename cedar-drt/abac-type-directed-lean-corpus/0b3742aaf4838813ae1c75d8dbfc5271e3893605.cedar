permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"6" in [action, principal])) && false
};
