permit(
  principal,
  action,
  resource
) when {
  (true && (a::"66" in [resource, a::"66", principal])) && false
};
