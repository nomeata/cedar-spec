permit(
  principal == a::"7",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"7" in [action, principal])) && false
};
