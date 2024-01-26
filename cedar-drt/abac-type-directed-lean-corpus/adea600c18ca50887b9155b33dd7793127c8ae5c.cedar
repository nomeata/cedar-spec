@A("\0\0A")
permit(
  principal,
  action,
  resource == z::"t6"
) when {
  true && ({"!6": false, "": resource in action} has "")
};
