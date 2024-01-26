@xTR("")
@xTT("")
@xss("")
permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource
) when {
  (true && ((ip("6\0")).isIpv4())) && false
};
