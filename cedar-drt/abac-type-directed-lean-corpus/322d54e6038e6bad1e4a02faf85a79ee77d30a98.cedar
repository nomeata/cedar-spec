permit(
  principal in ye::"67",
  action == Action::"action",
  resource is Ie in ye::""
) when {
  true && (action in Action::"action")
};
