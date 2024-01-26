forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && (principal["A"])) && principal
};
