permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"6" in (if ((ip("54;64.54.54")).isIpv4()) then [] else []))) && false
};
