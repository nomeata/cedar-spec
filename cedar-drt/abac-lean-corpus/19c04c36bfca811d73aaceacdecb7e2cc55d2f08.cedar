forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ((false == (false || principal)) is a)) && principal
};
