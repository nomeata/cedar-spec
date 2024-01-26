@A("\u{6}\0\0\0")
permit(
  principal == a::"n",
  action in [Action::"action"],
  resource
) when {
  true
};
