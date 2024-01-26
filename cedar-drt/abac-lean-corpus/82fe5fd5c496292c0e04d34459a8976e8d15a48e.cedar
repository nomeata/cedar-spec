permit(
  principal == a::"",
  action,
  resource
) when {
  (true && ((false in principal) in principal)) && principal
};
