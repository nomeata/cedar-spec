permit(
  principal == a::"\0",
  action,
  resource == a::""
) when {
  ((true && action) && context) && Action::""
};
