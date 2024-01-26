forbid(
  principal is a in a::"&jj\0",
  action in [Action::"action"],
  resource == a::"&jj\0"
) when {
  (true && (((context in a::"&jj\0") in principal) in false)) && principal
};
