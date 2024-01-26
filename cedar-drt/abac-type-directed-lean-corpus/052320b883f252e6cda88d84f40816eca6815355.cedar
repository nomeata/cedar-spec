forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (if ([true].contains(false)) then (a::"\002" is a) else false)) && true) && false
};
