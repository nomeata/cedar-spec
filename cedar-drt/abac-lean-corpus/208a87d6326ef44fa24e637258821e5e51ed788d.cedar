@A0041("\u{10}")
forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((a::"" == principal) || principal)
};
