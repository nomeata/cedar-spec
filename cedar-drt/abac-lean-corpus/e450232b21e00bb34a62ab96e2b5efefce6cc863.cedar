permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (principal.greaterThanOrEqual(false))) && false
};
