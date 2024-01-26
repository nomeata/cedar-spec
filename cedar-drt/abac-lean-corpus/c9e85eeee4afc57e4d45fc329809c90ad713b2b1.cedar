permit(
  principal == a::"h",
  action in [Action::"action"],
  resource
) when {
  (true && ((a::"" == ({"": ""}[""])).containsAny(({"": ""}[""])[""]))) && principal
};
