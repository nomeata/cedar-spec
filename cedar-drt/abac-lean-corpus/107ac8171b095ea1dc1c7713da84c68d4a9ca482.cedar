permit(
  principal == a::"j",
  action in [Action::"action"],
  resource is a
) when {
  (true && a::"j") && true
};
