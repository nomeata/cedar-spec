permit(
  principal is a,
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && (if "" then (principal in principal) else principal)
};
