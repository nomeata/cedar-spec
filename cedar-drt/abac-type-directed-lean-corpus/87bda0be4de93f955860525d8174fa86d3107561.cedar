permit(
  principal is a in a::"\0\0\0\u{1}\056",
  action == Action::"action",
  resource is a
) when {
  ((true && (a::"\0\0\0\u{1}\056" in principal)) && false) && true
};
