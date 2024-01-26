forbid(
  principal == A::a::"",
  action in [A::Action::"action"],
  resource
) when {
  ((true && (A::Action::"action" in A::Action::"action")) && (A::a::"" in principal)) && (A::a::"" in A::Action::"action")
};
