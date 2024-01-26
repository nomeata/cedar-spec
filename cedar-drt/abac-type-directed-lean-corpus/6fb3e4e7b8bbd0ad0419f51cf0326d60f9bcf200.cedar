permit(
  principal == a::"\"\"\"\"\"\"\"\"\"2\"\"\"\"",
  action in [Action::"action"],
  resource
) when {
  (true && (principal == principal)) && true
};
