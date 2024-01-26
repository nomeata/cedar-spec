permit(
  principal is a in a::"",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  true && ((ip("\u{1e}\u{1e}\u{1e}\u{1e}\u{1e}\u{1e}\u{1e}\0")) == principal)
};
