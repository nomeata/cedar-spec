@A("\0\0A")
permit(
  principal,
  action,
  resource == z::""
) when {
  true && ({"\0\0\0\0\0\0principa\0\0\0\0\0\0\0\0<\0\0\0\0": [false]} has "")
};
