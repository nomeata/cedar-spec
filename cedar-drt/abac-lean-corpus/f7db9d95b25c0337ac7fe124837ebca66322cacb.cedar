@r("\0l")
permit(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  true
};
