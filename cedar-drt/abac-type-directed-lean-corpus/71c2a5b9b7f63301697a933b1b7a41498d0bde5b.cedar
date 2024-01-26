forbid(
  principal == a::"2",
  action in [Action::"action"],
  resource == a::"2"
) when {
  ((true && (action is a)) && true) && true
};
