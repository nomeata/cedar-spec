@A("\0")
permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && (([true].contains(false)) == (a::"" is a))) && false) && false
};
