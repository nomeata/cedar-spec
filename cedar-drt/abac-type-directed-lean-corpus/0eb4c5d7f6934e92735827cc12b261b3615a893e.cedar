permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if ((ip("54.5ù.54.54")).isIpv4()) then principal else principal) is a)
};
