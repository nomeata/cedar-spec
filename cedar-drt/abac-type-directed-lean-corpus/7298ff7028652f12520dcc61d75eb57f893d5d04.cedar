permit(
  principal,
  action,
  resource is a in a::","
) when {
  true && (!(action in [action, principal, principal]))
};
