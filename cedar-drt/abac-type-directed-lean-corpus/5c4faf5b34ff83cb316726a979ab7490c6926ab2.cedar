permit(
  principal,
  action,
  resource
) when {
  (true && ((ip(principal["A"])).isIpv4())) && true
};
