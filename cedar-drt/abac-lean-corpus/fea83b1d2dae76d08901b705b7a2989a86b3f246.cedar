permit(
  principal is a,
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && (((if principal then principal else principal) == principal).lessThan(principal, principal, principal))
};
