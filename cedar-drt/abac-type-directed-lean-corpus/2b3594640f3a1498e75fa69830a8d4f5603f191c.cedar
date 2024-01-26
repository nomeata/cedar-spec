permit(
  principal in a::"6666\u{7}\0\u{1}\0\0\0\u{5}\0\0\u{1}\0\0\0\0\0\0\\",
  action in [Action::"action"],
  resource is a in a::"6666\u{7}\0\u{1}\0\0\0\u{5}\0\0\u{1}\0\0\0\0\0\0\\"
) when {
  (true && (a::"" is a)) && false
};
