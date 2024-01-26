forbid(
  principal,
  action,
  resource
) when {
  (true && ((if false then (ip("")) else (if false then (ip("::2b:36c9:cc33")) else (ip("0.0.0.0")))).isIpv4())) && false
};
