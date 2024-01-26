forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  true && (!((!([Amh00::"", false] < principal)) < Action::"action"))
};
