permit(
  principal,
  action,
  resource
) when {
  true && (principal in action)
};
