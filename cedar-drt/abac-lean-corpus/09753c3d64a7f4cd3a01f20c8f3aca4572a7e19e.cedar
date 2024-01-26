permit(
  principal is a,
  action == Action::"action",
  resource == a::""
) when {
  true && (principal.greaterThanOrEqual(if principal then (a::"&\0jtm\u{10}\0\0\0\0:\0\0lp" == false) else principal))
};
