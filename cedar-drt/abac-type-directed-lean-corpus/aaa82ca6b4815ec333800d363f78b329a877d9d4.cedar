forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if (true == false) then [[]] else [[], [], []]).containsAny([if false then [] else []]))
};
