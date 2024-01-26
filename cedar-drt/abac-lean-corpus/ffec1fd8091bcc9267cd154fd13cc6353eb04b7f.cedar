permit(
  principal == a::"j",
  action,
  resource
) when {
  ((true && (context == principal)) && principal) && principal
};
