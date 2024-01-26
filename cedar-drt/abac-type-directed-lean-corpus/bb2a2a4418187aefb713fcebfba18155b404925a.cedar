permit(
  principal is a in a::"\0\0\0\0\0\0\0\0\0\0\0\u{1}\057",
  action == Action::"action",
  resource is a in a::"\0\0\0\0\0\0\0\0\0\0\0\u{1}\057"
) when {
  (true && (a::"\0\0\0\0\0\0\0\0\0\0\0\u{1}\057" in principal)) && false
};
