permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((resource["BssX"]) == (if ((decimal("267658639500745.1135")) == (decimal("267658639500883.6901"))) then (if true then (decimal("0.1")) else (decimal("360259826557439.1807"))) else (principal["BssX"])))) && (Action::"action" in a::"")) && (action in action)
};
