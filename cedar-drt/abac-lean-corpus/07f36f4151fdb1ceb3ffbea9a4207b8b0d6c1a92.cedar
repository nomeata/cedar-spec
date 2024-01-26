permit(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  true && (!((!((!(Action::"action" < Action::"action")) < context)) < a::"r"))
};
