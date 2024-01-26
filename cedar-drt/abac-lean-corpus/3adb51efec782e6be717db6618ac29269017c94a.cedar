permit(
  principal == a::"\0jj\u{16}\0j",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::"i"
) when {
  ((true && a::"\0jj\u{16}\0j") && false) && principal
};
