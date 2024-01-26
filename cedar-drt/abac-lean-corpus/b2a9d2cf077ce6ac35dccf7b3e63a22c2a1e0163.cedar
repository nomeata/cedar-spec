forbid(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && ((("" in "") in a::"") in context)) && Action::"action") && ((("" in "") || (Action::"action" in false)) in principal)
};
