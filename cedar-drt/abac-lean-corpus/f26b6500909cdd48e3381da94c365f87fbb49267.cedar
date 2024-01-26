permit(
  principal is _,
  action == Action::"action",
  resource == _::"\u{17}"
) when {
  (true && (principal is A)) && principal
};
