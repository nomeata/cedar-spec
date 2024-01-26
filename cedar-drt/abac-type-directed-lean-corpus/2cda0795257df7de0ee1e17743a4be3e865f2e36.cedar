permit(
  principal,
  action,
  resource
) when {
  true && (if (if ((ip("03207.207.207")).isIpv4()) then false else false) then false else false)
};
