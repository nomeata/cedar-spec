forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"&j#\u{6}"
) when {
  true && (ip(""))
};
