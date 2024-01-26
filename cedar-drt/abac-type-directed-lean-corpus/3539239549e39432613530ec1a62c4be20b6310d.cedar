permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && ((action in action) || ((decimal("")).lessThanOrEqual(decimal(""))))) && (a::"" has "")
};
