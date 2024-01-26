permit(
  principal == a::"b",
  action in [Action::"action"],
  resource == a::"b"
) when {
  (true && (([false, Action::"action", Action::"action"].containsAll([true, E::"@\0\0", a::"b"])) == (!principal))) && a::"jjj"
};
