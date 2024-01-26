permit(
  principal,
  action,
  resource is a in a::"vz6.6"
) when {
  (true && ((a::"vz6.6"["C"]).isIpv4())) && ((ip(principal["z"])).isIpv4())
};
