permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (ip(context))) && principal
};
