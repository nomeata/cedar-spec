permit(
  principal,
  action,
  resource
) when {
  (false && (if ((ip("")).isIpv4()) then ((ip("")).isInRange(ip(""))) else ([principal, principal].containsAny([(-2767113589962061258), 3906369264536663606])))) && true
};
