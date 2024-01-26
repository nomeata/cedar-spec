permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (action in [a::",", action, a::""])) && (((if true then (ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")) else (ip("303:ffff:ffff:ffff:ffff:ffff:f6ff:ffff/3"))).isMulticast()) == false)
};
