permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (ip(false))) && principal
};
