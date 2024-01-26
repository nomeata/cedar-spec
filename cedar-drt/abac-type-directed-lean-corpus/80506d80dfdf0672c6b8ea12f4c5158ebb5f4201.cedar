forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((ip("6")).isIpv4())) && (if (action in action) then ((ip("")).isIpv4()) else ((decimal("\ti")).lessThanOrEqual(decimal(""))))
};
