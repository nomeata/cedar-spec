permit(
  principal,
  action in [AgAhh::Action::"action"],
  resource is AgAhh::a
) when {
  ((true && (principal["A"])) && false) && action
};
