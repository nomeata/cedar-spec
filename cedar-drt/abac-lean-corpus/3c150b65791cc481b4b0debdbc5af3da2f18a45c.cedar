permit(
  principal == a::"jj",
  action in [Action::"action"],
  resource is a in a::"jj"
) when {
  true && ((Action::"action" in false)[""])
};
