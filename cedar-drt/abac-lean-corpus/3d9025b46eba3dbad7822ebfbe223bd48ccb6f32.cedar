permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && (if false then (!false) else a::"")) && action
};
