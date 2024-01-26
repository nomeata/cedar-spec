forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && Action::"action") && (((Action::"action" in Action::"action") in (Action::"action" in a::"")) in principal)
};
