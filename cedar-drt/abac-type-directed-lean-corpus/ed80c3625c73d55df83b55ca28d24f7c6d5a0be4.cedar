permit(
  principal == a::"",
  action == Action::"action",
  resource == a::"666\0\0\0@\0\0\0\0\0\0\0\0\0:\u{1}\0\0\0\0\0\0[#"
) when {
  (true && (a::"" in [a::"666\0\0\0@\0\0\0\0\0\0\0\0\0:\u{1}\0\0\0\0\0\0[#", a::""])) && false
};
