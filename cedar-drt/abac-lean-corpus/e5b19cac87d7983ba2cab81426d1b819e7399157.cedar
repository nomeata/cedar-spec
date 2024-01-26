permit(
  principal == a::"\0l",
  action == Action::"action",
  resource
) when {
  (true && ("" && principal)) && principal
};
