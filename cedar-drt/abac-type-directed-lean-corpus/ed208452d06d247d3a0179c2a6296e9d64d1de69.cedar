forbid(
  principal is a in a::"",
  action in [Action::"action",Action::"action"],
  resource
) when {
  true && (action in resource)
};
