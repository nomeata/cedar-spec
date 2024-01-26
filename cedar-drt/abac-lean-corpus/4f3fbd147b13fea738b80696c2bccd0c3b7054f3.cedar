permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && a::"A\u{1}") && principal
};
