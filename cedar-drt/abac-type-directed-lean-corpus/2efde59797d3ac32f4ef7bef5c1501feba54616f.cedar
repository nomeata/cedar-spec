permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (a::"" in principal)) && false
};
