permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (false in context)) && false
};
