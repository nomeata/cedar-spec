permit(
  principal,
  action in [Action::"j;jj",Action::"j",Action::""],
  resource
) when {
  true && (false || principal)
};
