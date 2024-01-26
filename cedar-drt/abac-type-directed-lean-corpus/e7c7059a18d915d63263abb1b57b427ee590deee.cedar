permit(
  principal == a::"",
  action,
  resource
) when {
  ((true && ([ip("::f236:9c9c:9c94:9c24"), ip("0.0.0.0")].containsAll([]))) && false) && false
};
