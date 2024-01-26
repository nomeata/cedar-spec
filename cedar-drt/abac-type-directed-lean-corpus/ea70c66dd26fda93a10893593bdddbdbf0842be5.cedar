permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (action in [a::",", action, a::""])) && (((if true then (ip("ffff:ff27:2727:2723:c136:ca33:7a36:7a76/126")) else (ip("76.76.76.76"))).isMulticast()) == (!(!false)))
};
