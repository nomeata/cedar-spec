forbid(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (a::"" has "")
};
