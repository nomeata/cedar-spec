permit(
  principal,
  action in [Action::"action"],
  resource is a
) when {
  (true && (action in [a::"\0", action, a::","])) && (action in [a::",", action, a::""])
};
