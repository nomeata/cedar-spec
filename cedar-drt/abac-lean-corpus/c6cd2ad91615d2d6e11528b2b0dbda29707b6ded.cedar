@B("\0")
permit(
  principal,
  action,
  resource
) when {
  true && (((resource && resource) == resource) == context)
};
