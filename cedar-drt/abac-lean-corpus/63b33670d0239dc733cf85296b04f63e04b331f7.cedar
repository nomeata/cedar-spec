forbid(
  principal == a::"\u{2}\0",
  action in [Action::"action"],
  resource == a::"\u{2}\0"
) when {
  true && (((Action::"action" + Action::"action") == (a::"" in "")) has "")
};
