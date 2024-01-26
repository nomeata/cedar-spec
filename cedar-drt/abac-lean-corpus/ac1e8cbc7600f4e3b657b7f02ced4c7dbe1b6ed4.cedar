@B("\0")
permit(
  principal,
  action,
  resource
) when {
  true && (((resource has "p") == resource) == resource)
};
