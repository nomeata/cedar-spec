@r("\u{6}\0\0\0")
permit(
  principal,
  action in [A::Action::"action"],
  resource
) when {
  false
};
