@Ax00("\0\0")
permit(
  principal == a::"\0",
  action,
  resource in a::"\0"
) when {
  true
};
