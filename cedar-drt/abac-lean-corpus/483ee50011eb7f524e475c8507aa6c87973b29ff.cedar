@Ai000("\0K\\ccccc")
permit(
  principal == a::"j\u{1}9",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && principal) && true) && true
};
