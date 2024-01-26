permit(
  principal == a::"mpl",
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && ("".lessThan(false))
};
