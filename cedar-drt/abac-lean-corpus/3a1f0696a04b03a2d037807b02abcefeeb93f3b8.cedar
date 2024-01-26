forbid(
  principal is a in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::""
) when {
  ((true && (((Action::"action" has "") has "") has "")) && (((Action::"action" has "") has "") has "")) && (((if principal then principal else principal) has "") has "")
};
