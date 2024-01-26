forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && (({"": ip("41..1.0.54")}[""]).isIpv4())) && false
};
