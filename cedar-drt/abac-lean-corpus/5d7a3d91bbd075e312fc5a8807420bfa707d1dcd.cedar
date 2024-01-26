permit(
  principal,
  action in [Action::"action"],
  resource == a::"R"
) when {
  (true && [action, principal]) && Action::"action"
};
