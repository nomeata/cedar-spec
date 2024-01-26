permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (ip(principal))) && principal
};
