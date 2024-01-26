forbid(
  principal is a in a::"666",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && ([[]].containsAll(if ((ip("54.54.54.62")).isIpv4()) then [] else (if false then [] else [])))) && (action has "")) && (action has "")
};
