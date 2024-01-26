permit(
  principal == a::"",
  action,
  resource in a::""
) when {
  (true && (Action::"action" in context)) && ""
};
