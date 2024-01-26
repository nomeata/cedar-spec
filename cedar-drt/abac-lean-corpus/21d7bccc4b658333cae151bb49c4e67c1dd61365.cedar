permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([E::"*\0\0", a::""])) == true)) && true
};
