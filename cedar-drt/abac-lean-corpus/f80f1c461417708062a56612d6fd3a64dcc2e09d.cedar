permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  true && ((!Action::"action") is a)
};
