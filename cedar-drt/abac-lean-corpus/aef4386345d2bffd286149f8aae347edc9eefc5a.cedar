permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (principal in context)) && false
};
