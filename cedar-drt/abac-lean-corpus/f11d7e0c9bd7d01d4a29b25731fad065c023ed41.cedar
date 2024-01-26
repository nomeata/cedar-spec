permit(
  principal,
  action in [Action::""],
  resource is a in a::""
) when {
  true && (false || (if principal then principal else principal))
};
