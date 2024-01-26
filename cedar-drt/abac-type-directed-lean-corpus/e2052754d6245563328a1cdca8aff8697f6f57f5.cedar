permit(
  principal == r::"\0",
  action,
  resource is y in r::"\0"
) when {
  false
};
