permit(
  principal == a::"66",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if (true == false) then {} else {}) == {})) && false) && false
};
