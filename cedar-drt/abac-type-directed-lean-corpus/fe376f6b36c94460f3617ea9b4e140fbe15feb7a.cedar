@A("\0\0\0\0")
permit(
  principal,
  action,
  resource
) when {
  true && (action in principal)
};
