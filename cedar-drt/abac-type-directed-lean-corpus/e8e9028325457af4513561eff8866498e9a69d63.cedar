forbid(
  principal == a::"66",
  action == Action::"action",
  resource
) when {
  ((true && (!true)) && true) && true
};
