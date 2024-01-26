@psos("\u{3}")
permit(
  principal == a::"\0",
  action == Action::"action",
  resource
) when {
  true
};
