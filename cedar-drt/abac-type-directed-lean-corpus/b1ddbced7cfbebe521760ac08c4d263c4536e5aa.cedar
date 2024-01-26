permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  ((true && (if (if ((ip("54.50.207.207/15")).isMulticast()) then (if false then false else false) else ((ip("54.255.255.51/0")).isIpv4())) then false else false)) && false) && false
};
