permit(
  principal == a::"\0\0\0\0\0\u{1}",
  action,
  resource
) when {
  true && (resource in [Action::"action", a::"\0\0\0\0\0\u{1}", A9S99ssN0::""])
};
