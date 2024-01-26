permit(
  principal,
  action,
  resource is a
) when {
  (true && (a::"" == ((Action::"action" in a::"") + context))) && (!(!(!a::"")))
};
