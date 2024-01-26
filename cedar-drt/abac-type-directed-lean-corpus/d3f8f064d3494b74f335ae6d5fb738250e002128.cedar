permit(
  principal,
  action == Action::"action",
  resource is a in a::""
) when {
  ((true && (a::"" in principal)) && true) && false
};
