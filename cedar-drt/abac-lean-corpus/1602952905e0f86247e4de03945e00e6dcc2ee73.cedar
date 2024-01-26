permit(
  principal in a::"",
  action,
  resource
) when {
  (true && principal) && principal
};
