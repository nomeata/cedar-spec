@A("\0\0A")
permit(
  principal,
  action,
  resource == z::"t6"
) when {
  true && ({":666666\0;6666666666666\0366": false, "": false} has "")
};
