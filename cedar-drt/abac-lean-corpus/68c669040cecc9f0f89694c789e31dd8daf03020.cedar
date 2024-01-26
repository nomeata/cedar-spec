permit(
  principal == A::a::"ij\u{4}\0\0\0\0\0\0\0\0\0\0",
  action in [A::Action::"action",A::Action::"action"],
  resource is A::a in A::a::"ij\u{4}\0\0\0\0\0\0\0\0\0\0"
) when {
  (true && (((A::Action::"action" in false) in (A::Action::"action" in A::Action::"action")) in ((A::a::"" in 7657513547273863167) in principal))) && false
};
