@r("(")
@v("")
permit(
  principal == a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a
) when {
  true
};
