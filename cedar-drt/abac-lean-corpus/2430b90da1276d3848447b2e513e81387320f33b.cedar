permit(
  principal == a::"Djjjno",
  action == Action::"action",
  resource is a in a::"Djjjno"
) when {
  (true && (((Action::"action" in Action::"action") in []) in principal)) && principal
};
