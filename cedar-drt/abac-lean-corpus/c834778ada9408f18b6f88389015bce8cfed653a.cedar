permit(
  principal == a::"",
  action,
  resource
) when {
  (true && Action::"") && principal
};
