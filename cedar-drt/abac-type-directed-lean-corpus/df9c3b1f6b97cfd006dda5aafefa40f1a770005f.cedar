permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ((principal has "=======================================\u{2}\0\0\0\0\0\0======") == (principal has ""))) && true) && false
};
