permit(
  principal is a,
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && (mhhhc::"jtmpl".isLoopback(action, !false, action))
};
