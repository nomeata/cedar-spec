forbid(
  principal is a in a::"666",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && ([[]].containsAll(if ((ip("6.54.54.62/24")).isIpv4()) then [[], [], []] else []))) && (Action::"action" in a::"666")) && (action has "")
};
