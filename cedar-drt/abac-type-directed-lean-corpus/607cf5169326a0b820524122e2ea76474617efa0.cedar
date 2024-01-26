forbid(
  principal is a,
  action in [Action::"action"],
  resource == a::"\u{16}666"
) when {
  false
};
