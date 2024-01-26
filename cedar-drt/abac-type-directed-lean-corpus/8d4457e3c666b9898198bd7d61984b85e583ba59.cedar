permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (a::"6\0\0\0Z" in [a::"6\0\0\0Z", resource, Action::"action"])) && true) && (resource == principal)
};
