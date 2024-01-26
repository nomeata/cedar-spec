permit(
  principal is a,
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && (principal.lessThan(!(!principal), !(resource == principal), resource))
};
