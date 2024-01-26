@BssH("\0\0\0\0\0\0\06666")
permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource == a::"6"
) when {
  true && ((ip(principal["Boss"])).isIpv4())
};
