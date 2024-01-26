permit(
  principal == a::"j",
  action == Action::"action",
  resource
) when {
  (true && (false in (context && context))) && Action::"action"
};
