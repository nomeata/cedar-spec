@r("\u{6}\0\0\0")
permit(
  principal == A::a::"\u{18}\0\0",
  action in [A::Action::"action"],
  resource == A::a::""
) when {
  true
};
