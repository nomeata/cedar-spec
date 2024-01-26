permit(
  principal == a::"j",
  action,
  resource == a::"j"
) when {
  (true && (a::"\0\0\0\0"["\0\u{5}\0jjjjjjjjjjjjjjjjjjSet\0"])) && a::"\0\0\0\0"
};
