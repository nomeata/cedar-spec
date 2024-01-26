permit(
  principal in a::"\0ji\nj\0                 ",
  action == Action::"action",
  resource in a::"\0ji\nj\0                 "
) when {
  true
};
