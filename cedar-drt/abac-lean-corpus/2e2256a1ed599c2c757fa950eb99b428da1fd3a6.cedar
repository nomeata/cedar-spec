forbid(
  principal == Ahchh::"",
  action in [Action::"action"],
  resource
) when {
  (true && principal) && Action::"action"
};
