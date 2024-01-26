permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (false in principal)) && Action::"action"
};
