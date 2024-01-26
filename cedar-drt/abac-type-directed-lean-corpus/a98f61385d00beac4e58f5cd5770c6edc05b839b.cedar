permit(
  principal is a in a::"",
  action,
  resource is a in a::""
) when {
  (true && (a::"" has "z")) && ((ip("")).isIpv4())
};
