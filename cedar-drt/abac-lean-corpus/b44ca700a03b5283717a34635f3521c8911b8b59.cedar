@r("\u{1}\0")
permit(
  principal,
  action,
  resource
) when {
  true && (((a::"cc" in resource) == resource) == action)
};
