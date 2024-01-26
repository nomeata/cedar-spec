@A000i("\0H3ccccc")
permit(
  principal == a::"j",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && principal) && true) && true
};
