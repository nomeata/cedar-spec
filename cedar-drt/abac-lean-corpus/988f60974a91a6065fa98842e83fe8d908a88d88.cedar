permit(
  principal == a::"jjj",
  action in [Action::"action"],
  resource == a::"jjj"
) when {
  (true && (a::"" is a)) && false
};
