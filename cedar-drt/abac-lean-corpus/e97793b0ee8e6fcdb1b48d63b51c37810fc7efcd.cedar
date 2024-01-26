permit(
  principal is a in a::"j",
  action in [Action::"action"],
  resource == a::"\r"
) when {
  (true && Action::"action") && (!false)
};
