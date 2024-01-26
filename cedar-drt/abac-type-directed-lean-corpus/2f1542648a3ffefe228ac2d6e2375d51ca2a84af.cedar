permit(
  principal == a::"4-6\0o\u{1}\0\0\06",
  action,
  resource is a in a::"4-6\0o\u{1}\0\0\06"
) when {
  (true && ((if false then [] else []).containsAny([]))) && true
};
