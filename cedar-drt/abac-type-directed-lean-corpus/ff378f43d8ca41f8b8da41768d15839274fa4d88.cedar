forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (resource in a::"t\0\022A")) && (!true)) && false
};
