forbid(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && ((("" has "on") == (false has "")) == true)
};
