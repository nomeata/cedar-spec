forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && (a::""["A"])) && principal
};
