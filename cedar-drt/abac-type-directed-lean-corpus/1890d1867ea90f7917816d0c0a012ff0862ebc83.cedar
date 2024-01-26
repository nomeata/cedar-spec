permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && (principal in action)) && false
};
