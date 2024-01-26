forbid(
  principal,
  action,
  resource
) when {
  ((true && (a::"" in [resource, principal, action])) && false) && false
};
