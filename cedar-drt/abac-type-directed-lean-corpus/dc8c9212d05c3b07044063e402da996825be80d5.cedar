permit(
  principal == a::"6\0",
  action in [Action::"action"],
  resource
) when {
  (true && (!((decimal("6")).lessThanOrEqual(decimal(""))))) && (action has "")
};
