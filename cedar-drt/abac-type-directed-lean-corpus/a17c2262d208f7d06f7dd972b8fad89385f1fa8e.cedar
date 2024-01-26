permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if (principal has "d") then (decimal("")) else (decimal(""))) == (decimal("")))) && (action has "")) && true
};
