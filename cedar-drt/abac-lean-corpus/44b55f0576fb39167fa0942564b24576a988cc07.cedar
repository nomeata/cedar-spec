forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && {"A": false}) && principal
};
