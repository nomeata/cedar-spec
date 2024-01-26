permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  (true && (((Action::"action" in C::"") in (Action::"action" in principal)) in principal)) && principal
};
