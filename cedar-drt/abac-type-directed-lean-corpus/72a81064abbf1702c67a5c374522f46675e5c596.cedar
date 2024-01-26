permit(
  principal == a::"\0\0\0:\065\0",
  action in [Action::"action"],
  resource
) when {
  ((true && (if (Action::"action" in a::"\0\0\0:\065\0") then true else (!false))) && false) && false
};
