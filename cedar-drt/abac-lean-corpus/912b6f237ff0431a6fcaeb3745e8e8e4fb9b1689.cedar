forbid(
  principal is A::a in A::a::"",
  action in [A::Action::"action"],
  resource
) when {
  true && (A::Action::"action".isIpv6())
};
