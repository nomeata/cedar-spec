permit(
  principal,
  action in [Action::""],
  resource is a in a::""
) when {
  true && (a::"" || principal)
};
