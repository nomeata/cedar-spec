forbid(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  (true && ((![a::"", "j", false, principal]) is a)) && principal
};
