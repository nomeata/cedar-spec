permit(
  principal == a::"\0\0\0\0\0",
  action in [Action::"action"],
  resource
) when {
  true && (Acr0c::"" is a)
};
