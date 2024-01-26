permit(
  principal == a::"633",
  action,
  resource == a::"633"
) when {
  true && ((if ((ip("127.65.57.255/21")).isMulticast()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isMulticast())
};
