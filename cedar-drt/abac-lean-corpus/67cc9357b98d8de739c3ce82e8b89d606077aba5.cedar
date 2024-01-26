forbid(
  principal in A::r::a::"",
  action == A::r::Action::"action",
  resource in A::r::a::""
) when {
  (true && (((A::r::Action::"action" == A::r::Action::"action") == (A::r::Action::"action" == A::r::Action::"action")) == ((A::r::Action::"action" == A::r::Action::"action") == (A::r::Action::"action" == principal)))) && principal
};
