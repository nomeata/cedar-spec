forbid(
  principal == a::"J",
  action in [Action::"action"],
  resource
) when {
  ((true && (((!principal) is a) is a)) && Action::"action") && ((!(false is a)) is a)
};
