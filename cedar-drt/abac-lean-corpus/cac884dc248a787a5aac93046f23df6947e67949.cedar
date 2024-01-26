permit(
  principal in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && [true, !principal, false, context]) && a::"") && a::""
};
