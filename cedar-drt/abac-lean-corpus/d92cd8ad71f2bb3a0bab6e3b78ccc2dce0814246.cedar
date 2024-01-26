permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (!(if principal then principal else (context == action)))) && a::""
};
