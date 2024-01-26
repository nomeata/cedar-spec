forbid(
  principal == a::"666",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && ([] == [])) && false) && false
};
