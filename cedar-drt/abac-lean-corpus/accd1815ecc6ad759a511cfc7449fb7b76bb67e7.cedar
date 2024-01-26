permit(
  principal == a::"\u{6}",
  action in [Action::"action"],
  resource
) when {
  (true && Action::"action") && (!a::"")
};
