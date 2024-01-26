forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (((!(Action::"action" <= context)) in false) in context)) && true) && action
};
