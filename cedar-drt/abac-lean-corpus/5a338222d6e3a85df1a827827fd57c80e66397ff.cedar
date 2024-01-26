permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  true && ("\0".containsAll(principal))
};
