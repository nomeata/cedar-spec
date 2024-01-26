forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ("" in (("" in "") in (if principal then principal else principal)))) && principal
};
