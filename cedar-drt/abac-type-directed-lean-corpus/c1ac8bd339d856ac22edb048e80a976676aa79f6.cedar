@A("\0\0A")
permit(
  principal,
  action,
  resource == z::"t6"
) when {
  true && ({"!\0\0\0\0\0\n\0r03\0": false} has "")
};
