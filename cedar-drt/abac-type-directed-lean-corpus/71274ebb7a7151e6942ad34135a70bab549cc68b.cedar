permit(
  principal is a in a::"7",
  action in [Action::"action"],
  resource is a in a::"7"
) when {
  (true && ((ip(if true then "" else "")).isInRange(ip("::ff99:9acd:dff")))) && false
};
