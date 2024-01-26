permit(
  principal in a::"",
  action,
  resource
) when {
  true && ((Action::"action" == a::"z").containsAny(true.contains(false)))
};
