permit(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  ((true && ([[false, true, false], [true], []].contains([(ip("22.64.0.54")).isIpv6(), resource in action]))) && false) && true
};
