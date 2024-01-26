permit(
  principal is a,
  action == Action::"action",
  resource == a::"mp"
) when {
  true && (mh000::"\0\0\0\0\0".isLoopback(principal, principal, action))
};
