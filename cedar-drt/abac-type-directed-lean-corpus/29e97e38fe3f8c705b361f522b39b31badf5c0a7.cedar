permit(
  principal == a::"6\u{3}",
  action in [Action::"action",Action::"action"],
  resource is a in a::"6\u{3}"
) when {
  (true && ([[], [false]].containsAny(if ((ip("54.54.54.54")).isIpv4()) then (if true then [] else []) else []))) && false
};
