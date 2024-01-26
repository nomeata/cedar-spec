permit(
  principal,
  action,
  resource is a in a::""
) when {
  ((true && (false in context)) && principal) && principal
};
