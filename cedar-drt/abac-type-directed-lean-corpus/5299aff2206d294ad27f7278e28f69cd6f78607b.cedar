permit(
  principal is a in a::"6\u{1}i",
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  true && (a::"6\u{1}i" in principal)
};
