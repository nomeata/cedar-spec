forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ((Action::"action" == action).containsAny([false == a::"r", !("zpij," < true)]))) && (false.isIpv6())
};
