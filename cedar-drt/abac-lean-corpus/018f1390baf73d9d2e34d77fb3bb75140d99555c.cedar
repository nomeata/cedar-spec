@A("\0")
permit(
  principal,
  action == Action::"action",
  resource == a::"\0\0\0\0\0\0\0\0\0"
) when {
  true
};
