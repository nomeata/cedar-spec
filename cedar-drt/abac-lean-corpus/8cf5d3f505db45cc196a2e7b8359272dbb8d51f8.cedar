permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (decimal(context))) && Action::"action"
};
