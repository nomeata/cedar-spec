permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && (a::"" == (!(a::"" == a::"\u{10}\0\0")))
};
