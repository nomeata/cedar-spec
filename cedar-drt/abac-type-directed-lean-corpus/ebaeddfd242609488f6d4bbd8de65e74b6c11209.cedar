permit(
  principal is A::a in A::a::"6\0",
  action in [A::Action::"action"],
  resource is A::a in A::a::"6\0"
) when {
  (true && (A::a::"u" in principal)) && true
};
