@r("\u{1}\0")
permit(
  principal,
  action,
  resource
) when {
  true && (((resource in resource) == resource) == resource)
};
