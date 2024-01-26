forbid(
  principal is a in a::"67",
  action in [Action::"action"],
  resource == a::"67"
) when {
  (true && (({"": action, "ppp": []}[""]) in principal)) && false
};
