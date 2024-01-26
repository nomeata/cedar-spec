@A("\0\0\u{1}")
permit(
  principal is a in a::"\0\0\t",
  action == Action::"action",
  resource
) when {
  false
};
