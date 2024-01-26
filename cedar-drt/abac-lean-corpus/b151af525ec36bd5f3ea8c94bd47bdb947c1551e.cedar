permit(
  principal == a::"bjjj",
  action in [Action::"action"],
  resource == a::"jjjjj&jj\0\0"
) when {
  (true && principal) && a::"jjjjj&jj\0\0"
};
