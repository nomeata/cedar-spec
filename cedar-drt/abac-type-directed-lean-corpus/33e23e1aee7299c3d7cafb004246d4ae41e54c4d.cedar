@A("\0\0\0\0\0\0\0\0\u{11}\0A")
permit(
  principal,
  action,
  resource == z::"t6"
) when {
  true && ({"": ip("")} has "")
};
