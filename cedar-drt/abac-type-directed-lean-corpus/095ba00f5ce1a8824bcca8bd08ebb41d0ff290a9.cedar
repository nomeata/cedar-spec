forbid(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && (!(!((ip("::ff:39ff:ffff:4d:c6fe:3637")).isMulticast())))) && false) && false
};
