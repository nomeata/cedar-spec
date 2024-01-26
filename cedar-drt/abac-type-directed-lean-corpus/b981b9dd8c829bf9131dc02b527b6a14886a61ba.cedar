@tp("3\u{1}")
forbid(
  principal == a::"66",
  action in [Action::"action"],
  resource == a::"66"
) when {
  (true && ((ip(principal["Bsss"])).isIpv4())) && false
};
