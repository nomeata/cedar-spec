permit(
  principal,
  action,
  resource
) when {
  (false && (if ((ip("6\u{16}6")).isIpv4()) then ((ip("6\0")).isInRange(ip("\06\0\0A13"))) else ({"": false} has ""))) && false
};
