permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && ((("" in 0) in principal) in principal)) && principal
};
