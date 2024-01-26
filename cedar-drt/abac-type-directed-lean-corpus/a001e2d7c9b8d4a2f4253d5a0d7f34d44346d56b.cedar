permit(
  principal,
  action == Action::"action",
  resource is a in a::""
) when {
  (true && ((ip("::c2f2:c9c9")) == (ip("0.0.0.0")))) && false
};
