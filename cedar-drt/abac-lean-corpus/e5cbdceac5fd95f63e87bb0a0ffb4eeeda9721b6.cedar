permit(
  principal == A::a::"\u{1c}\"\0\0\0\0",
  action in [A::Action::"action",A::Action::"action"],
  resource is A::a in A::a::"\u{1c}\"\0\0\0\0"
) when {
  (true && (context in ([] in (A::Action::"action" in A::Action::"action")))) && (false in principal)
};
