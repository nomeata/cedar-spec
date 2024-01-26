permit(
  principal == a::"jjj",
  action in [Action::"action"],
  resource
) when {
  (true && a::"jjj") && (!(!(!principal)))
};
