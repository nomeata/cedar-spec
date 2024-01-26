forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && (!((ip("76")).isMulticast()))
};
