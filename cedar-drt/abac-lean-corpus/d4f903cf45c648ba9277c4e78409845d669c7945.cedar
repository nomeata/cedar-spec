permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"" in 106)) && principal
};
