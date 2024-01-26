permit(
  principal == a::"6666",
  action in [Action::"action",Action::"action"],
  resource == a::"6666"
) when {
  ((true && ([] == [])) && true) && false
};
