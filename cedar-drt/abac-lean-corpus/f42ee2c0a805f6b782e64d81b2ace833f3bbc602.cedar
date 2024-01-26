permit(
  principal is a,
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && [[A0000::"".containsAll(principal), principal], principal]) && principal
};
