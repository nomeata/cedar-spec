forbid(
  principal in a::"6",
  action in [Action::"action"],
  resource
) when {
  ((true && ([] == [])) && true) && false
};
