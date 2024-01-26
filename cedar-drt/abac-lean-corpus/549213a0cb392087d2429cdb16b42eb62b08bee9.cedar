forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && Action::"action") && (((Action::"action" in Action::"action") in principal) in principal)
};
