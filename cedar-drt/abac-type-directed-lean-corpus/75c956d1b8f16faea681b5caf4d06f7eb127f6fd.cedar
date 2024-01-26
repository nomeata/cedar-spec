@X000("\0A")
permit(
  principal,
  action,
  resource == z::"t"
) when {
  true && ({"": ip(""), "!6666666663": false} has "")
};
