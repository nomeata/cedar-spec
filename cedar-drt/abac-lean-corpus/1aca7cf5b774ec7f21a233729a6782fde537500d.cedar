permit(
  principal == a::"\0\u{4}@\u{10}\0",
  action in [Action::""],
  resource
) when {
  (true && (((!false) == principal) == action)) && Action::""
};
