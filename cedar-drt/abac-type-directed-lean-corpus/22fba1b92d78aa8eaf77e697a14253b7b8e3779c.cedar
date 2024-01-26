permit(
  principal,
  action,
  resource in a::"7"
) when {
  (true && (Action::"action" in principal)) && false
};
