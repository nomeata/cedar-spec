permit(
  principal == AhhgA::a::"",
  action in [AhhgA::Action::"action"],
  resource is AhhgA::a
) when {
  ((true && (principal["r00"])) && principal) && action
};
