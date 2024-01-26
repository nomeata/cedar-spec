forbid(
  principal == a::"",
  action,
  resource
) when {
  (true && Action::"action") && false
};
