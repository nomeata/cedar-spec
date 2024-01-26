permit(
  principal,
  action in [Action::"action"],
  resource == a::"R"
) when {
  (true && [Action::"action" || principal, context]) && context
};
