permit(
  principal is a,
  action == Action::"action",
  resource == a::"HHAHHHHHHXHH\0\0\0\0\0\0\0\u{16}m"
) when {
  true && (a::"HHAHHHHHHXHH\0\0\0\0\0\0\0\u{16}m".isIpv6())
};
