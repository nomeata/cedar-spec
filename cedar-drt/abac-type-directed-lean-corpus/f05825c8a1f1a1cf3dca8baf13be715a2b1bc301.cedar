@B("66666665\u{7}\0\0\0\0\0")
@B111Y1("\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\0\0\0\0\0\0\0\0\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}=\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}")
@n("\0\0")
@r("EuEEEEEE")
permit(
  principal is a in a::"665\u{7}\0\0\0\0\0",
  action in [Action::""],
  resource is a in a::"665\u{7}\0\0\0\0\0"
) when {
  (true && ((ip("w\u{16}")).isIpv4())) && ((if (action in principal) then Action::"11537" else a::"665\u{7}\0\0\0\0\0") in action)
};
