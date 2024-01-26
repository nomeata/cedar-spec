permit(
  principal == a::"\0",
  action,
  resource
) when {
  true && (false is a)
};
