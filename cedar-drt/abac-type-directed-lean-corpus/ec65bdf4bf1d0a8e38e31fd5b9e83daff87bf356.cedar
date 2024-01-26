permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((!([].containsAll([]))) == (a::"6" in Action::"action"))) && (principal is a)) && ((ip("/6")).isLoopback())
};
