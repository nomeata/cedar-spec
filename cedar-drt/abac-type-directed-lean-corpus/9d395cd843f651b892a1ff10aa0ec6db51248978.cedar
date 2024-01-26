permit(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((action is a) && (principal in principal))) && (principal in action)
};
