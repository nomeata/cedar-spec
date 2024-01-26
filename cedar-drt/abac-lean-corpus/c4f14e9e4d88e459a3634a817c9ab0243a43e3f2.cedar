permit(
  principal is a,
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && (a::"mpl".isIpv4())
};
