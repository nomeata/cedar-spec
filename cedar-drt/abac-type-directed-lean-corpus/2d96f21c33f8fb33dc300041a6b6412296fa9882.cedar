forbid(
  principal,
  action == Action::"action",
  resource is a in a::""
) when {
  (true && (a::"" is a)) && ([[false, false], if false then [] else [], [[], []]].containsAny([]))
};
