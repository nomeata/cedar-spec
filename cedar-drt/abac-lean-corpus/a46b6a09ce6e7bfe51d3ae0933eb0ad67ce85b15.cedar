permit(
  principal,
  action in [Action::"action"],
  resource == a::"R"
) when {
  (true && [Action::"action" || context, a::"R"]) && a::"R"
};
