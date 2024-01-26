permit(
  principal == a::"",
  action,
  resource
) when {
  ((true && ([ip(""), ip("36.36.36.36")].containsAll([]))) && false) && false
};
