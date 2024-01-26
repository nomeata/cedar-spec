permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && (a::""["\0\0"])) && context
};
