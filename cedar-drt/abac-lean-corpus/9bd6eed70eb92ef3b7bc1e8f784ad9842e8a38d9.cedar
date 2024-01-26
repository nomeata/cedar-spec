permit(
  principal == a::"jj",
  action == Action::"action",
  resource in a::"jj"
) when {
  ((true && (a::"ccc" == ((7710162557904524808 * 3276800) || principal))) && principal) && action
};
