permit(
  principal is a,
  action in [],
  resource is a in a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
) when {
  true && Action::"action"
};
