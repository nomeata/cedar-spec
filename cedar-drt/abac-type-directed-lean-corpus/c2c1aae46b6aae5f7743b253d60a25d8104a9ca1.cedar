permit(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (false == (A::a::"" has ""))) && (principal has "")
};
