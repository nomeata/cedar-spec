@A("\0\0662667z3nnnn")
@qnxpllllllV2303("n\0\0\0\0\0\0\0\u{16}\0\0\0")
@r("nnn6e6666606666;6")
permit(
  principal,
  action,
  resource
) when {
  (true && ([resource, if true then action else action, resource].contains(resource))) && (resource in resource)
};
