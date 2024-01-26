permit(
  principal == q300s0000000000::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ((if (principal has "") then (decimal("")) else (decimal(""))) == (decimal("")))) && (action has "ri")) && false
};
