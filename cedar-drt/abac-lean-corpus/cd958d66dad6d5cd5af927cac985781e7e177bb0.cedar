forbid(
  principal == a::"\0",
  action,
  resource
) when {
  (true && "") && (An100::"".containsAll(principal))
};
