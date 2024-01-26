permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && (((decimal("6")).lessThanOrEqual(decimal(""))) || (action has ""))) && (action has "6")
};
