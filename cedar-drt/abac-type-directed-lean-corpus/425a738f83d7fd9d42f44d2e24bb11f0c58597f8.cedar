permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource == a::"6"
) when {
  (true && ((ip("")).isIpv4())) && (action has "")
};
