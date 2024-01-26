forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && ((("" == "") in ("z" in "")) in principal)) && principal
};
