permit(
  principal == a::"jjjj",
  action in [Action::""],
  resource
) when {
  ((true && action) && A1000::"\0\0\0\0") && (!action)
};
