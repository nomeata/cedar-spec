permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && action) && (action == principal)
};
