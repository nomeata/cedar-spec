permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && (((principal has "cons") in principal) has "")
};
