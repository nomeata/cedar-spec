permit(
  principal == a::"\u{7f}\u{7f}\u{7f}\u{7f}\u{7f}ZZZZZZZZZZZZZZ$ZZZZZZZZZZZZZZZZZZ",
  action in [Action::"uuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuutujAjjjj",Action::"#jjjjjj",Action::""],
  resource == a::"\0\0\0\0\0\0\0+\0\0\0\0\0\0j"
) when {
  ((true && a::"\0\0\0\0\0\0\0+\0\0\0\0\0\0j") && a::"\0\0\0\0\0\0\0+\0\0\0\0\0\0j") && principal
};
