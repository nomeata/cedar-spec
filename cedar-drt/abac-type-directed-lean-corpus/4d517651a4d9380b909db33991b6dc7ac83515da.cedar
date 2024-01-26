forbid(
  principal == a::"667",
  action == Action::"action",
  resource == a::"667"
) when {
  (true && ([] == [])) && false
};
