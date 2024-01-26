permit(
  principal,
  action,
  resource == a::"j\0\0\0\0\0\0\0\0\0\0"
) when {
  (true && (a::""["\0\u{5}\0\0\0\0\0{\0\0jjjjjjjjjjjjjjjjjjjjjjjjjjjjjj"])) && a::""
};
