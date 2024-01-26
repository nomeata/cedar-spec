permit(
  principal == a::"<6\0+\0\0\u{1}\0\0\u{1}\0\0\06",
  action,
  resource is a in a::""
) when {
  (true && ([decimal("\0"), decimal("\0")].containsAny([false == false, false]))) && true
};
