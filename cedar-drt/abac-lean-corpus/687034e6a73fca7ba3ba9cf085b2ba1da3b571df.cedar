permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([true, a::"j", mhhch::"j\0\0\0"].containsAll("")) == false)) && principal
};
