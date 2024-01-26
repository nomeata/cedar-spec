@_("d")
@r("\u{2}\u{2}\u{2}\u{2}\u{2}\u{2}\u{2}")
permit(
  principal in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && ((if ((ip("255.255.255.183/24")).isInRange(ip("ff0f:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"))) then 144680345676153346 else 144680345676153346) == 144680345676153346)) && ([[[], []], [[], []]] == [[[], []], [[], []]])
};
