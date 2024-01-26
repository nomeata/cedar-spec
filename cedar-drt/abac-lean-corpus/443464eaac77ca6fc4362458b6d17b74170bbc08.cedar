permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && action) && (((action == a::"") == (action == action)) == principal)
};
