permit(
  principal in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (principal in principal)) && false
};
