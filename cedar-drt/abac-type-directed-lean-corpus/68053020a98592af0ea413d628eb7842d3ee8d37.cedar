permit(
  principal == a::"7\u{1}i",
  action == Action::"action",
  resource == a::"7\u{1}i"
) when {
  ((true && ([].containsAll([]))) && false) && (action has "")
};
