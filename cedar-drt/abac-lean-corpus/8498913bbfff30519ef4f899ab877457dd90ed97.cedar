permit(
  principal is a,
  action == Action::"action",
  resource == a::""
) when {
  true && (context.isIpv4())
};
