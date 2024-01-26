forbid(
  principal is a in a::"\u{2}\0",
  action in [Action::"action"],
  resource in a::""
) when {
  true && (((a::"" == a::"") == (a::"" == a::"")) == ((a::"" == a::"") == (a::"" == a::"")))
};
