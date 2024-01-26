permit(
  principal == a::"aation6",
  action == Action::"action",
  resource is a in a::"aation6"
) when {
  (true && ((if ((ip("29.0.54.177//118")).isIpv4()) then (ip("")) else (ip(""))).isIpv6())) && (action has "66")
};
