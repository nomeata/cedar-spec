permit(
  principal is a in a::"6ooooooooooooooooooooooo",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"6ooooooooooooooooooooooo" in [action, principal])) && false
};
