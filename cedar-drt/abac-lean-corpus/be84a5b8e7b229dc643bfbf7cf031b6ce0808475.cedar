@r("\u{1}\0")
permit(
  principal,
  action,
  resource
) when {
  true && (((resource && resource) == resource) == resource)
};
