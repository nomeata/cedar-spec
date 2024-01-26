permit(
  principal,
  action,
  resource
) when {
  ((true && ((if false then (ip("255.51.0.0/24")) else (ip("0.0.0.0"))).isIpv4())) && false) && false
};
