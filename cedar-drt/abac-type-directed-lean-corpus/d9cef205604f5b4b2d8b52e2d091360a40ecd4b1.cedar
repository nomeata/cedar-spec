permit(
  principal,
  action in [Action::"action"],
  resource is a
) when {
  (true && (action in [a::",", action, a::""])) && true
};
