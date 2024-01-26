permit(
  principal,
  action,
  resource
) when {
  (true && ((if ((ip("55.0.0.0/23")).isIpv6()) then [] else []) == [])) && false
};
