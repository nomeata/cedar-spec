forbid(
  principal == M::"",
  action,
  resource is M in BcpD::""
) when {
  (true && ((if true then (ip("")) else (ip("33"))).isIpv4())) && (if false then true else true)
};
