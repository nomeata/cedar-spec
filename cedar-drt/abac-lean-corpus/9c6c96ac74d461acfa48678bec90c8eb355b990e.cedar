forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && (((a::"i" == action) || "") in principal)) && principal
};
