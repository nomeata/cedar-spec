forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::"idj\0\0@"
) when {
  (true && ("" && context)) && false
};
