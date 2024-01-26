permit(
  principal is a,
  action == Action::"action",
  resource == a::"\u{6}\u{6}\u{6}\u{6}\u{6}\u{6}tmpl"
) when {
  true && (principal.lessThan())
};
