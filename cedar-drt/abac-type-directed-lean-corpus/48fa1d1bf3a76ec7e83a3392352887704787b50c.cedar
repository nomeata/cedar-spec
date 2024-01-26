permit(
  principal,
  action in [Action::"action"],
  resource == a::"666"
) when {
  false && (!(!(principal in principal)))
};
