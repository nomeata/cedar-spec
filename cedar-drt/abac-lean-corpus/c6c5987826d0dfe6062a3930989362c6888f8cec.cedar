@r("\u{1}\0")
permit(
  principal,
  action,
  resource
) when {
  true && (((principal in principal) == principal) == principal)
};
