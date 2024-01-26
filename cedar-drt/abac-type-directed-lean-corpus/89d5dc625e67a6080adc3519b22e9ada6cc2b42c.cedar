forbid(
  principal in a::"\0",
  action == Action::"action",
  resource == a::"\0"
) when {
  true
};
