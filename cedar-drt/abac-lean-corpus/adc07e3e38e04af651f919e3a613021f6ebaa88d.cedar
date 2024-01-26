permit(
  principal,
  action,
  resource == a::"mjiJ\0\u{3}\0\0\0"
) when {
  (true && (![Action::"action" has ""])) && false
};
