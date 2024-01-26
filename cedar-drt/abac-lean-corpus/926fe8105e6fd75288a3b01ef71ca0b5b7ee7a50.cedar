permit(
  principal is a,
  action == Action::"action",
  resource == a::"l"
) when {
  true && (a::"l".isIpv4())
};
