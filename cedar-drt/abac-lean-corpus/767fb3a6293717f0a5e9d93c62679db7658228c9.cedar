forbid(
  principal,
  action,
  resource in a::""
) when {
  (true && (context["A"])) && principal
};
