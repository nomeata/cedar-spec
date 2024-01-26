permit(
  principal == a::"",
  action == Action::"action",
  resource == a::"666\0\0\0\0\0\0\0\u{8}\0\0\0\0\0\0\0\0\0\0\0\0\0\0:\u{1c}"
) when {
  (true && (action in principal)) && true
};
