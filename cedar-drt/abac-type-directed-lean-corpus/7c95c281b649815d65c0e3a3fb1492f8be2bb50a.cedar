permit(
  principal is a in a::"\0\0\0\06",
  action in [Action::"action"],
  resource == a::"\0\0\0\06"
) when {
  ((true && ((if ((decimal("0.1")) == (decimal("0.1"))) then (if true then (decimal("0.1")) else (decimal("0.1"))) else (decimal(""))) == (decimal("@")))) && ((ip("@")).isIpv6())) && (!(action in action))
};
