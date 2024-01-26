permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (false.isIpv6())) && action
};
