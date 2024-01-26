permit(
  principal is a in a::"66\0\u{12}6",
  action in [Action::"action",Action::"action"],
  resource is a in a::""
) when {
  (true && ((a::"" has "") || (action has ""))) && (principal has "7")
};
