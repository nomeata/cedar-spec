permit(
  principal,
  action,
  resource
) when {
  (true && (if resource then (context == (!principal)) else principal)) && principal
};
