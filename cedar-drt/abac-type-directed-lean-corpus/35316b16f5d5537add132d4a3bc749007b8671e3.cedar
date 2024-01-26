permit(
  principal,
  action,
  resource is a in a::"\0\0\0\0\0\0\0\0\0\0"
) when {
  true && (a::"\0\0\0\0\0\0\0\0\0\0" has "")
};
