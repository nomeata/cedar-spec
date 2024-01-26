permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (action in [a::",", action, a::""])) && (((if true then (ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")) else (ip("ff69:65ff:ffff:ffff:fff:ffff:ffff:ffff/126"))).isMulticast()) == (!(!false)))
};
