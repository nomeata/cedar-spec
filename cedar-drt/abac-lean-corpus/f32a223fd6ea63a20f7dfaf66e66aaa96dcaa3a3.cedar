forbid(
  principal,
  action,
  resource is a in a::""
) when {
  (true && ([] in ((Action::"action" in Action::"action") in false))) && principal
};
