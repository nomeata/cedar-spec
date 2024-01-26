@r("\u{1})\0")
permit(
  principal,
  action,
  resource
) when {
  true && (((action in principal) == (!true)) == principal)
};
