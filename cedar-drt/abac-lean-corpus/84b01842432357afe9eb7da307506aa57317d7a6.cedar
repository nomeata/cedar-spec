permit(
  principal == a::"j",
  action in [Action::"action"],
  resource is a in a::"j"
) when {
  true && [Action::"action", a::"j", true]
};
