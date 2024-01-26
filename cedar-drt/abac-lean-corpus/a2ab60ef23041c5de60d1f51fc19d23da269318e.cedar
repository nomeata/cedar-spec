permit(
  principal == a::"\0\0\u{8}",
  action,
  resource == a::"\0\0\u{8}"
) when {
  (true && "i\0") && (principal == principal)
};
