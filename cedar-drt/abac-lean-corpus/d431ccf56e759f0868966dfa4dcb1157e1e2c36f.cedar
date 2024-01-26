permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (((principal has "on_con") == principal) == principal)
};
