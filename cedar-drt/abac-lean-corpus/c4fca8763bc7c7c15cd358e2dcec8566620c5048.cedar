permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"\0\u{4}"
) when {
  ((true && ([principal, action] <= a::"")) && Action::"action") && Action::"action"
};
