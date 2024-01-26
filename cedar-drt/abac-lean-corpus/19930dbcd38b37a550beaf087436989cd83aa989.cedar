permit(
  principal,
  action == Action::"action",
  resource == a::"\0"
) when {
  (true && (!principal)) && ((principal && principal) && principal)
};
