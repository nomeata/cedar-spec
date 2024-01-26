permit(
  principal,
  action in [Action::""],
  resource
) when {
  (true && ((ip(resource["BcpD"])).isIpv4())) && ((if ((decimal("922337203685477.5807")) == (decimal("922337203685477.5807"))) then (ip("")) else (ip(""))).isMulticast())
};
