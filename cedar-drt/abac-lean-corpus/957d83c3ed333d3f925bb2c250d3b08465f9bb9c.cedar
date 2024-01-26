permit(
  principal == a::"jj\0",
  action,
  resource == a::"jj\0"
) when {
  true && ([a::"", false] is a)
};
