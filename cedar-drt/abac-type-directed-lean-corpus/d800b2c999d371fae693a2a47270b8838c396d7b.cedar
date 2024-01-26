permit(
  principal == a::"\0\0\0\0\0\0\0",
  action in [Action::"action"],
  resource
) when {
  true && (resource in [Action::"action", a::"\0\0\0\0\0\0\0", A9S99ss0N::""])
};
