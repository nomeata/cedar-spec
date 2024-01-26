forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (((Action::"action" in Action::"action") + (A::"" + principal)) in principal)) && principal
};
