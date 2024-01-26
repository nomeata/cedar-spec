permit(
  principal,
  action,
  resource in a::""
) when {
  true && ((if principal then principal else false) in true)
};
