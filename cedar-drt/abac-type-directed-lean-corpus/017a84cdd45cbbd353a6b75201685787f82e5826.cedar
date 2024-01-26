permit(
  principal == a::"6",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  ((true && (action has "P100")) && (action has "P100")) && ((ip("")).isIpv4())
};
