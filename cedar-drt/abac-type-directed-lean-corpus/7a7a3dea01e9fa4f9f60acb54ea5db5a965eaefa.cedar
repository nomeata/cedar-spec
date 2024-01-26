forbid(
  principal == A::a::"\06\u{1}6\u{5}\0\0\0\0\0\0",
  action == A::Action::"action",
  resource is A::a in A::a::"\06\u{1}6\u{5}\0\0\0\0\0\0"
) when {
  false && (A::a::"\06\u{1}6\u{5}\0\0\0\0\0\0" in principal)
};
