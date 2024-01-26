permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (!(Action::"action".containsAll(if principal then principal else principal)))
};
