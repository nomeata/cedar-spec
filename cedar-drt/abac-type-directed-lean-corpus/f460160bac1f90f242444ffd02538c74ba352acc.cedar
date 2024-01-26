permit(
  principal == a::"",
  action,
  resource
) when {
  ((true && ([[principal, principal], [principal, principal], [[]]].containsAll([]))) && true) && true
};
