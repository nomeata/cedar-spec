permit(
  principal == _::"",
  action in [Action::"action",Action::"action"],
  resource in _::""
) when {
  ((true && (principal == _::"")) && false) && principal
};
