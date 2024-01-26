permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  (true && (action is a)) && true
};
