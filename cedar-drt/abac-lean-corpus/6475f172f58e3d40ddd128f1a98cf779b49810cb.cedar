permit(
  principal == a::"\0\0\0\0\0\0\0",
  action in [Action::"action"],
  resource is a in a::"\0\0\0\0\0\0\0"
) when {
  (true && ([ip(""), false["\0"]] is a)) && principal
};
