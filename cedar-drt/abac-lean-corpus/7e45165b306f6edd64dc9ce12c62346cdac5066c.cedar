@r("\0jj\0\0\0")
permit(
  principal == a::"jjj",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((!(context == a::"jjj")) == a::"jjj")
};
