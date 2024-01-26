permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::"R"
) when {
  true && (Action::"action" || (principal == action))
};
