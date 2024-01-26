permit(
  principal == a::"6",
  action == Action::"action",
  resource is a
) when {
  true && (if ([true, true, true].contains(principal in principal)) then true else false)
};
