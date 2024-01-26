permit(
  principal,
  action,
  resource
) when {
  true && (((resource has "p") == (resource in resource)) == context)
};
