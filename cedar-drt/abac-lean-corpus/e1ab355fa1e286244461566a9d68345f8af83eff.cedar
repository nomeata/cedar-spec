forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (((!(Action::"action" <= Action::"action")) in principal) in context)) && true) && resource
};
