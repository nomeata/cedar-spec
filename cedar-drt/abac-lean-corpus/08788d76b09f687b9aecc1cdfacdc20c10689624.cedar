forbid(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, Action::"action", false].contains(a::"" in Action::"action")) == resource)) && [Action::"action", a::"j"]
};
