permit(
  principal == a::"jjjbjj",
  action in [Action::"action"],
  resource == a::"jjjbjj"
) when {
  (true && (([true, Action::"action", a::""].contains(Action::"action")) == principal)) && a::""
};
