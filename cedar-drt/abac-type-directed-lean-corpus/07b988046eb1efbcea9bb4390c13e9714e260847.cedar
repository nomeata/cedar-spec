permit(
  principal is a in a::"6ooooooooooooooooooooooooooooooo",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"6ooooooooooooooooooooooooooooooo" in [resource, principal])) && false
};
