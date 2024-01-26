permit(
  principal,
  action,
  resource
) when {
  (true && ({"A": if principal then principal else principal}[""])) && principal
};
