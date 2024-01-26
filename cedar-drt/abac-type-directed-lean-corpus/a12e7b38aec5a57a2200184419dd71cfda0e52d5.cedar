permit(
  principal == a::"6context66",
  action in [Action::"action",Action::"action"],
  resource == a::"6context66"
) when {
  ((true && ((if ((ip("40.1105.129.116/221")).isMulticast()) then [] else []) == [])) && false) && false
};
