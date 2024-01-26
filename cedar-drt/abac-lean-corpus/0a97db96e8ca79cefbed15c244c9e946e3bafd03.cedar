permit(
  principal,
  action in [Action::"action"],
  resource == a::"\0idjj"
) when {
  (true && Action::"action") && false
};
