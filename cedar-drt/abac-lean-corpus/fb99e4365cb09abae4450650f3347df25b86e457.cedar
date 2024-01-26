permit(
  principal in a::"mpl",
  action in [Action::"action"],
  resource == a::"mpl"
) when {
  true && ("".isLoopback())
};
