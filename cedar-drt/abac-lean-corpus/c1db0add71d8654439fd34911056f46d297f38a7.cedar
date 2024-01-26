forbid(
  principal,
  action,
  resource == a::""
) when {
  ((true && a::"") && ((("" in "z") in (false in principal)) in principal)) && principal
};
