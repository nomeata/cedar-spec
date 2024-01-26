@r("X")
permit(
  principal is a in a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && principal) && principal
};
