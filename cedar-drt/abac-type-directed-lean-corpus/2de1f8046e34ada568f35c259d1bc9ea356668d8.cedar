@A("\0\0A")
permit(
  principal,
  action,
  resource == z::"t6"
) when {
  (true && ({"": []} has "\0\0\0\0\0")) && false
};
