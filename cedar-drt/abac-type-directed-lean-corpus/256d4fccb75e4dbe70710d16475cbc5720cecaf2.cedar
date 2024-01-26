forbid(
  principal in a::"6",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && ((if (principal has "\u{17}\0\0\0\0\0\0\0!66:>6`6") then a::"" else a::"") has "\u{17}\0\0\0\0\0\0\0!66:>6`6")
};
