forbid(
  principal == a::"*&jj\0\0\0",
  action in [Action::"action"],
  resource in a::"*&jj\0\0\0"
) when {
  true && ((("MM" == "") == (!false)) == (principal[""]))
};
