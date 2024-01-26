permit(
  principal is a in a::"&6",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if ((ip("54.36.38.0/ù1")).isIpv4()) then (if false then principal else principal) else a::"") is a)
};
