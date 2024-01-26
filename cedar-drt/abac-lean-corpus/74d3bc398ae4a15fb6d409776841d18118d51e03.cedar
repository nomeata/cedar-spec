permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  true && ((!a::"j") is a)
};
