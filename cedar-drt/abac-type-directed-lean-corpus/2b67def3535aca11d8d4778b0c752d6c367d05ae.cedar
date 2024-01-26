permit(
  principal == a::"6",
  action,
  resource
) when {
  (true && (principal in [])) && false
};
