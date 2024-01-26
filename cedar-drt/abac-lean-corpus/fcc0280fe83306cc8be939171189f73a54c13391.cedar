forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && principal) && (!principal)
};
