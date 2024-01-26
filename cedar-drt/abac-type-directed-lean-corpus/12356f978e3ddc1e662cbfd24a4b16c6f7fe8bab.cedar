@B("66666665\u{7}\0\0\0\0\0")
@B11111("\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}=\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}\u{1}")
@n("\0\0")
@r("EuEEEEEE")
permit(
  principal is a in a::"",
  action in [Action::"537"],
  resource is a in a::""
) when {
  (true && ((ip("w\u{16}")).isIpv4())) && ((if (action in principal) then Action::"6666+6666666e666666666;6" else a::"") in action)
};
