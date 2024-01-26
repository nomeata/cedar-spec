forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ((Action::"action" == action).containsAny([false == a::"r", !("zpij" < resource)]))) && (decimal(false))
};
