forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && (a::"c"["A"])) && context
};
