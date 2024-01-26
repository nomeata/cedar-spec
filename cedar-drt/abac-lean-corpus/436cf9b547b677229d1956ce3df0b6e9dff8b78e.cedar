permit(
  principal == a::"R",
  action == Action::"action",
  resource == a::"R"
) when {
  (true && action) && principal
};
