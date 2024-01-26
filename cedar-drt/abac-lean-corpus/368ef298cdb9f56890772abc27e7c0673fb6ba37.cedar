permit(
  principal == a::"j",
  action == Action::"action",
  resource
) when {
  (true && (false in (context && action))) && Action::"action"
};
