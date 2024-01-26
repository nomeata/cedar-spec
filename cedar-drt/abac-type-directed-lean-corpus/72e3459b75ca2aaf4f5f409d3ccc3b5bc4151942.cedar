@a("")
permit(
  principal == r::"co\u{11}\u{11}\u{11}",
  action == Action::"action",
  resource == r::"co\u{11}\u{11}\u{11}"
) when {
  true && ([[true]].containsAll([if true then true else true]))
};
