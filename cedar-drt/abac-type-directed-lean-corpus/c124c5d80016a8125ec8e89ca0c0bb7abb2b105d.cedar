permit(
  principal == a::"\0\0\0\u{1}",
  action in [Action::"action"],
  resource == a::"\0\0\0\u{1}"
) when {
  true && (({"": action, "l": [], "e": []}["e"]).contains({"": []}[""]))
};
