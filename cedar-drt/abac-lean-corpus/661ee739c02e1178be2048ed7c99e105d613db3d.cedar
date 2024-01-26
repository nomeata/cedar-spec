permit(
  principal is a,
  action,
  resource is a in a::""
) when {
  true && {"A": principal, "b": if principal then principal else principal}
};
