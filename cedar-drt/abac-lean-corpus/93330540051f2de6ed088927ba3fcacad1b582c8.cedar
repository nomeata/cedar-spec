@r("\u{6}\0\0\0")
permit(
  principal == A::a::"",
  action in [A::Action::"action"],
  resource
) when {
  true
};
