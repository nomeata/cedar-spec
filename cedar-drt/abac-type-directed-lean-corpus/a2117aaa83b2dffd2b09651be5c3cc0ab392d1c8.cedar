forbid(
  principal,
  action in [Action::"action"],
  resource is a
) when {
  true && ({"": if true then (decimal("0.1")) else (decimal("0.1"))} == {"": Action::"action"})
};
