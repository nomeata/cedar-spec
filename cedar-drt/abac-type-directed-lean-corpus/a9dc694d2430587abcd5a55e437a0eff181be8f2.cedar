permit(
  principal,
  action in [Action::"action"],
  resource is a
) when {
  (true && (action in [a::",", a::",", action])) && (action in [a::"\0", action, a::""])
};
