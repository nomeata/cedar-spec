permit(
  principal in a::"mpl",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ("".isLoopback())
};
