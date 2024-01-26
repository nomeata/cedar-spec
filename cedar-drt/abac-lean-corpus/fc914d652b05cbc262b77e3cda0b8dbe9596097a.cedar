forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((a::"" == false) || a::"")
};
