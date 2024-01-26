@A("\0\0662666z3nnn")
@qnxpllllllV2303("n\0\0\0\0\0\0\0\u{16}\0\0\0")
@r("nnn9e466666666;6")
forbid(
  principal,
  action in [Action::""],
  resource
) when {
  (true && ([resource, if true then action else action, resource].contains(resource))) && (resource in resource)
};
