permit(
  principal in a::"\0\0\0\0\0\0\0\0666\0",
  action in [Action::"action"],
  resource is a in a::"\0\0\0\0\0\0\0\0666\0"
) when {
  true
};
