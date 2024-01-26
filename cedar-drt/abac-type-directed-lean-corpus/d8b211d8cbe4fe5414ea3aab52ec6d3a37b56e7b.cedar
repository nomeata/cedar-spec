forbid(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && (principal is a)) && ([[], [], []].containsAll([]))) && false
};
