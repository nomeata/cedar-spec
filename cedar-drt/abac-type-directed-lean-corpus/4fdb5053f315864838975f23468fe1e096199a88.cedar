forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((ip("")).isIpv4())) && (action has "N")) && (principal has "")
};
