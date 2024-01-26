permit(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"66bbbbbbbbbbbbbbbbbbbbbbbbbbb"
) when {
  (true && (resource in [a::"66bbbbbbbbbbbbbbbbbbbbbbbbbbb", a::"66bbbbbbbbbbbbbbbbbbbbbbbbbbb"])) && (a::"66bbbbbbbbbbbbbbbbbbbbbbbbbbb" in a::"66bbbbbbbbbbbbbbbbbbbbbbbbbbb")
};
