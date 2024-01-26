forbid(
  principal is a in a::"67",
  action in [Action::"action"],
  resource == a::"67"
) when {
  (true && (({"": resource, "po6": []}[""]) in action)) && true
};
