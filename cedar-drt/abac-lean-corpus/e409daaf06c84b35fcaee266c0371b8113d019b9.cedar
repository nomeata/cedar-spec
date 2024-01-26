permit(
  principal in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (if context then context else context)) && context
};
