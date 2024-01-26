permit(
  principal,
  action,
  resource == a::""
) when {
  true && (resource && (!(principal == resource)))
};
