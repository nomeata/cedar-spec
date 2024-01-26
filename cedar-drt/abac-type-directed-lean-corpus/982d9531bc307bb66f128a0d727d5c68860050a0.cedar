permit(
  principal in a::"6",
  action in [Action::"action"],
  resource in a::"6"
) when {
  (true && (({"": decimal("504744192339614.5800")}[""]).lessThan(decimal("")))) && ((ip("")).isIpv4())
};
