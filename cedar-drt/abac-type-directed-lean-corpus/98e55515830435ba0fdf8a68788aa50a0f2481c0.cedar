forbid(
  principal == a::"\0\u{8}\0\022A",
  action in [Action::"action"],
  resource == a::"\0\u{8}\0\022A"
) when {
  ((true && (a::"" in a::"")) && false) && false
};
