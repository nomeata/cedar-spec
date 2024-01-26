@A("")
@AjwFp("3\u{1}\0\0\0")
@B("6")
@B00333("")
@J30t0k33("")
@lygbcdxt0000("\0\u{2}")
@r("\u{3}\u{4}\0-")
permit(
  principal,
  action,
  resource
) when {
  ((true && ([a::"", action].contains(resource))) && ("AAAAAA8AAAAAAAAAAAAAAAAAA\0" == "")) && ((ip("\06")).isIpv4())
};
