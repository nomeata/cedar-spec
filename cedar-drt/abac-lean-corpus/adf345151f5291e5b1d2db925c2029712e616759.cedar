forbid(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (((false.contains(principal)) == principal) == principal)
};
