permit(
  principal,
  action,
  resource is a
) when {
  (true && (resource in resource)) && ({} == {"": false})
};
