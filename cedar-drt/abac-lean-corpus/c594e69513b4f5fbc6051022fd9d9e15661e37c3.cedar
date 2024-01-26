forbid(
  principal == a::"\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::"\0\0"
) when {
  (true && (!((a::"\0\0" + a::"\0\0") < a::"\0\0"))) && ""
};
