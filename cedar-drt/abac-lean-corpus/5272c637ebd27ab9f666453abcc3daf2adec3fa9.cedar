forbid(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  true && (false || (a::"" == a::""))
};
