@A("\0\0A")
permit(
  principal,
  action,
  resource == z::""
) when {
  true && ({"x\0\0\0\0\0\0\0": false} has "\0\0\0\0\0")
};
