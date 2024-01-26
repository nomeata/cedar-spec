forbid(
  principal is e0s in e0s::"",
  action in [Action::"action"],
  resource
) when {
  true && (action has "")
};
