permit(
  principal == a::"mpl",
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && (mhhhc::"jtmpl".isLoopback(action, !(!action), true))
};
