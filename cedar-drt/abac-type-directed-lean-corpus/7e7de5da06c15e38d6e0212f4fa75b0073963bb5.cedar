permit(
  principal,
  action in [Action::"action"],
  resource in a::""
) when {
  ((true && ((if (!true) then (decimal("")) else (decimal("?"))) == (decimal(if true then "" else "")))) && ((if (resource in resource) then (if true then resource else resource) else (if true then resource else resource)) in (if (principal in principal) then a::"" else a::""))) && false
};
