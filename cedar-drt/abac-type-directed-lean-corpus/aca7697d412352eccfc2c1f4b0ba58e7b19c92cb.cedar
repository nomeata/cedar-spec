permit(
  principal == a::":::\0\0\0\u{7f}:",
  action in [Action::"action"],
  resource is a
) when {
  (true && (principal has "As")) && ((principal has "As") && (principal has "As"))
};
