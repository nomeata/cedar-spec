permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (decimal(Action::"action"))) && a::"\0\0\0\0\0\0\0\0\0\0"
};
