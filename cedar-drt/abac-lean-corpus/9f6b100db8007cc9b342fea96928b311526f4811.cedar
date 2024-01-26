permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (A::"" in principal)) && principal
};
