@r("\u{7f}tmpl")
permit(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  true
};
