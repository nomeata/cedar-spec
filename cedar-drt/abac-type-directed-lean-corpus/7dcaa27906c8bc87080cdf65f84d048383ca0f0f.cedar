forbid(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  true && ([[false, false], if false then [] else []].containsAny([[false, false], if false then [] else []]))
};
