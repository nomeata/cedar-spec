@A("\0\0662667z3nnnn")
permit(
  principal,
  action,
  resource
) when {
  (true && ([resource, if true then action else principal, a::""].contains(resource))) && false
};
