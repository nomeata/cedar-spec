permit(
  principal,
  action == Action::"action",
  resource == a::"\0\0\0\0\0\0\u{16}\0\0\0Y\u{16}66666>6666666"
) when {
  true && (!(action in resource))
};
