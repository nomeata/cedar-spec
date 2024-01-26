permit(
  principal is A::A::a in A::A::a::"6666>666\0",
  action in [A::A::Action::"action",A::A::Action::"action"],
  resource is A::A::a in A::A::a::"6666>666\0"
) when {
  ((true && (if (a::".$\0\0\0" in resource) then ((ip("")).isIpv4()) else (action has ""))) && (action has "")) && (A::A::a::"6666>666\0" has "\0\0\0\0")
};
