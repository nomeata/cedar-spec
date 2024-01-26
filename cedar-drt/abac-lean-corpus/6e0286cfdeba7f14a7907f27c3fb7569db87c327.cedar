permit(
  principal,
  action in [Action::"action"],
  resource == a::"\0\0\0\0"
) when {
  true && (!true)
};
