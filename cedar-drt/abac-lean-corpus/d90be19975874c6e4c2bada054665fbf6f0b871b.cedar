permit(
  principal == a::"j",
  action in [Action::"action"],
  resource in a::"j"
) when {
  ((true && (a::"ccc" == ((7710162557904524808 * 3276800) || action))) && true) && (if context then ((context + action) in true) else false)
};
