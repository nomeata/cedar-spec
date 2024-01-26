permit(
  principal is a in a::"6oooooooooooooooooooooooooooooooo",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"6oooooooooooooooooooooooooooooooo" in [resource, principal])) && false
};
