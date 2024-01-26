permit(
  principal,
  action,
  resource == a::"66(666665"
) when {
  (true && (["AAAAA\0\0\0YAAAAAAAAAAAAAAA"].containsAny([]))) && false
};
