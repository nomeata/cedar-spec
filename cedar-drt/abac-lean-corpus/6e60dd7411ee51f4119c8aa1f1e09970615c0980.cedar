@A("\0\0\0j\0j\0\u{1}\u{6}\u{1}\0j\0\0")
@m("jjjj")
@r("")
forbid(
  principal,
  action,
  resource
) when {
  (true && resource) && principal
};
