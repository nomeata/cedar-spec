forbid(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::"2"
) when {
  true && (Action::"action" has "")
};
