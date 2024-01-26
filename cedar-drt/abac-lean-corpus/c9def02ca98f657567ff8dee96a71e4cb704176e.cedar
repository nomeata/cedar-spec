@r("\u{1}\0\u{7}")
permit(
  principal,
  action,
  resource
) when {
  true && (((resource in resource) == (resource in principal)) == "")
};
