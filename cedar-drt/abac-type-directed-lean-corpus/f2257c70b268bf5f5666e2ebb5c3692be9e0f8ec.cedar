@A("\0\0\0\0\u{2}6\n")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ([false].containsAll([]))
};
