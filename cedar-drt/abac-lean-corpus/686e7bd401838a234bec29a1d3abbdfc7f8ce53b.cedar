permit(
  principal == a::"l",
  action in [Action::"action"],
  resource is a in a::"l"
) when {
  true && (if {"r": principal, "A": false} then principal else principal)
};
