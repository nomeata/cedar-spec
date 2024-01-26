@BDsT("66\u{1a}\u{1a}\u{1a}")
permit(
  principal == a::"2",
  action in [Action::"action"],
  resource == a::"2"
) when {
  (true && ((((ip("54.54.54.54/0")).isLoopback()) || false) || ([].containsAll([])))) && true
};
