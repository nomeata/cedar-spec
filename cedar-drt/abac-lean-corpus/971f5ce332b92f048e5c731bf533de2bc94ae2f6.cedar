@r("@")
forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && context) && false) && Action::"action"
};
