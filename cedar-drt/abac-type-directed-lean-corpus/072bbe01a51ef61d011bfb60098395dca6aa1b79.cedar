@A("\0\0662667z3nnnn")
@E("nn6e666666666;6")
@qnxpllllllV2303("n\0\0\0\0\0\0\0\u{16}\0\0\0")
permit(
  principal,
  action,
  resource
) when {
  (true && ([if true then action else action, resource, resource].contains(resource))) && (resource in resource)
};
