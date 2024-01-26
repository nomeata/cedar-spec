permit(
  principal,
  action,
  resource == a::"l"
) when {
  (true && Action::"action") && [context]
};
