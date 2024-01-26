forbid(
  principal,
  action,
  resource in a::""
) when {
  true && (if resource then principal else principal)
};
