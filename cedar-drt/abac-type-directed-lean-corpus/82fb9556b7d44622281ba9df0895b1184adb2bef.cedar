forbid(
  principal == a::"",
  action,
  resource
) when {
  ((true && ([if true then (ip("70.36.36.36")) else (ip("0.0.0.0")), ip("0.0.0.0")].containsAll([]))) && false) && false
};
