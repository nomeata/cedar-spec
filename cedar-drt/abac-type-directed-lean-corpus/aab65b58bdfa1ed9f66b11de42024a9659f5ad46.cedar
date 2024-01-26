permit(
  principal == a::"46\0o\u{1}\0\0\06",
  action,
  resource is a in a::"46\0o\u{1}\0\0\06"
) when {
  (true && ([decimal("\0"), decimal("\0")].containsAny([false, false]))) && false
};
