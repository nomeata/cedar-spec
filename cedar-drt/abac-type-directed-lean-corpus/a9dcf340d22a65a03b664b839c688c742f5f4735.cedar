permit(
  principal is a in a::"6666",
  action in [Action::"=[\u{7}",Action::"=[\u{7}"],
  resource is a in a::""
) when {
  true && (action has "")
};
