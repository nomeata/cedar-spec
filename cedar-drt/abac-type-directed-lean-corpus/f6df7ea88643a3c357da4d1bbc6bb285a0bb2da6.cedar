permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ([if false then "" else "", "", ""].contains(""))
};
