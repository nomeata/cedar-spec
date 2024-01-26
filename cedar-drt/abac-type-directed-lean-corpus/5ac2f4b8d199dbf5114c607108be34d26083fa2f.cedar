@A("")
permit(
  principal == a::"53",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::"53"
) when {
  false
};
