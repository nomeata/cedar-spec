permit(
  principal,
  action,
  resource
) when {
  true && (a::"" in resource)
};
