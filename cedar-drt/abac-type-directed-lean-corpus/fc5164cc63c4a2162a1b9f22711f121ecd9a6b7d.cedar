permit(
  principal is a in a::"6",
  action in [Action::"action",Action::"action"],
  resource is a in a::"6"
) when {
  true && (action has "")
};
