permit(
  principal is a,
  action,
  resource == a::"l\0`"
) when {
  (true && ((principal.greaterThan(principal)).greaterThan(principal))) && principal
};
