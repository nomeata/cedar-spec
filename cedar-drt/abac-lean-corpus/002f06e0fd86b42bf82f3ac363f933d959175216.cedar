permit(
  principal is a,
  action == Action::"action",
  resource == a::"&\0\0\u{f}\0\0\0pl"
) when {
  true && ("".greaterThanOrEqual(a::"&\0\0\u{f}\0\0\0pl"))
};
