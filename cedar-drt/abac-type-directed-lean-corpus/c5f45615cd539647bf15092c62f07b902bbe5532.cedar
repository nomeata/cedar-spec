permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (action in [a::",", action, a::""])) && true
};
