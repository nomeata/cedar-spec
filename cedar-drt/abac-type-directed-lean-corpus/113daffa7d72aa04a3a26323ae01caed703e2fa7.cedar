forbid(
  principal == a::"6662",
  action in [Action::"action"],
  resource == a::"6662"
) when {
  ((true && (action is a)) && (action has "67")) && (action has "6")
};
