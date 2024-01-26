permit(
  principal is a in a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\u{1}",
  action,
  resource
) when {
  true && (resource in [Action::"action", a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\u{1}", principal])
};
