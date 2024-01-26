forbid(
  principal == A::a::"\0\0\0\u{5}\06\u{1}6\u{5}\0\0\0\0\0\0\06666",
  action == A::Action::"action",
  resource is A::a in A::a::"\0\0\0\u{5}\06\u{1}6\u{5}\0\0\0\0\0\0\06666"
) when {
  false && (A::a::"\0\0\0\u{5}\06\u{1}6\u{5}\0\0\0\0\0\0\06666" in principal)
};
