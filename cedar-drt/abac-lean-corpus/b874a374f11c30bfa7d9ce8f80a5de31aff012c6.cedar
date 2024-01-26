permit(
  principal == a::"\u{5}",
  action == Action::"action",
  resource == a::"\u{5}"
) when {
  (true && resource) && true
};
