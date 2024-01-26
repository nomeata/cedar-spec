permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  ((true && (a::"ccc" == ((7710162557904524808 * 3276800) || action))) && true) && (if context then false else principal)
};
