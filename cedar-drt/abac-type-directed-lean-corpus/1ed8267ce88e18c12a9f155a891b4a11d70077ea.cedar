permit(
  principal,
  action in [Action::"action"],
  resource in a::""
) when {
  ((true && ((if (!true) then (decimal("")) else (decimal(""))) == (decimal(if true then "" else "")))) && (Action::"action" in a::"")) && false
};
