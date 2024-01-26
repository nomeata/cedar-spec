permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (((context || principal) || principal) || principal)) && principal) && principal
};
