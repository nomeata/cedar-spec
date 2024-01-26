permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && (((Action::"action" in Action::"action") in (Action::"action" in a::"")) in principal)) && principal
};
