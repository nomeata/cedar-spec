permit(
  principal is A::a in A::a::"6666",
  action in [A::Action::"action"],
  resource is A::a in A::a::"6666"
) when {
  (true && ((ip("666\0&o")).isIpv4())) && (!(resource in action))
};
