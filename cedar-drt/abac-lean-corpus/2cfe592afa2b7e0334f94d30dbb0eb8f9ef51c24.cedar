forbid(
  principal == A::a::"",
  action in [A::Action::"action"],
  resource is A::a in A::a::""
) when {
  (true && (((A::a::"ij\u{4}\0\0\0\0\0\0\0\0" has "") in [A::a::"ij\u{4}\0\0\0\0\0\0\0\0", context, action, context, false, A::a::"ij\u{4}\0\0\0\0\0\0\0\0", principal]) in false)) && A::a::"ij\u{4}\0\0\0\0\0\0\0\0"
};
