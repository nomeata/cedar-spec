forbid(
  principal == j::z::a::"2\u{1}\0",
  action,
  resource is j::z::a in j::z::a::"2\u{1}\0"
) when {
  false
};
