forbid(
  principal is a in a::"",
  action in [Action::"action",Action::"action"],
  resource == a::"\0\0"
) when {
  true
};
