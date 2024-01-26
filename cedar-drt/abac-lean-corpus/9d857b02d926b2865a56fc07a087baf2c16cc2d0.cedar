permit(
  principal is a in a::"jj",
  action in [Action::"action"],
  resource is a in a::"jj"
) when {
  (true && (((Action::"action" in Action::"action") in (Action::"action" in false)) in principal)) && principal
};
