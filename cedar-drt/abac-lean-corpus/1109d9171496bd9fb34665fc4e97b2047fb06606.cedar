permit(
  principal == a::"",
  action,
  resource
) when {
  true && action
};
