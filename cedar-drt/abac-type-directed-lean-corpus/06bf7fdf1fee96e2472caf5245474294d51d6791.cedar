permit(
  principal,
  action == Action::"action",
  resource
) when {
  (false && ((if false then (ip("")) else (ip(""))).isIpv4())) && true
};
