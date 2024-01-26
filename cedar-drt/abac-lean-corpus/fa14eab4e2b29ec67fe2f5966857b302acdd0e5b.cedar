permit(
  principal == a::"\0",
  action,
  resource is a in a::"\0"
) when {
  true
};
