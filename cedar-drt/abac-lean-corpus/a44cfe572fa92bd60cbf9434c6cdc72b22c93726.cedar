permit(
  principal == a::"\0",
  action,
  resource == a::"\0"
) when {
  (true && (Action::"action" == (!(principal && principal)))) && principal
};
