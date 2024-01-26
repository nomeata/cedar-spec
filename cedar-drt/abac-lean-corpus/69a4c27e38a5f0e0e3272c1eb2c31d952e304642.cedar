permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && (A0220::"" in principal)) && principal
};
