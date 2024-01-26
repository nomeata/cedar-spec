permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (a::"\u{16}666" in [resource, a::"\u{16}666", action])) && true) && false
};
