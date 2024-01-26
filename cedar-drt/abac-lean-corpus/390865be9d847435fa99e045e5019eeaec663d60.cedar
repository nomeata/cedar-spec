permit(
  principal == a::"t\0",
  action == Action::"action",
  resource
) when {
  (true && (a::"" && a::"")) && a::""
};
