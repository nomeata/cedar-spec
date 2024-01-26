@r("\u{1}\0")
forbid(
  principal,
  action in [Action::"ef"],
  resource is a in a::""
) when {
  true
};
