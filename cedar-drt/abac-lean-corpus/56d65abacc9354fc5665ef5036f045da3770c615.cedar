permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (decimal(Action::"action"))) && a::"j\0\0\0\0\0\0\0\0\0"
};
