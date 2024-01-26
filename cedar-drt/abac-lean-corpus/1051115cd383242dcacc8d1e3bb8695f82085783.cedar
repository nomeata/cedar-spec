permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"jr"
) when {
  true && action
};
