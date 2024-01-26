permit(
  principal is a in a::"",
  action in [Action::"action",Action::"action"],
  resource
) when {
  true && ((decimal("0.1")).lessThanOrEqual(decimal("00..1")))
};
