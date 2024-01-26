permit(
  principal,
  action in [Action::"j;jj",Action::"",Action::"j;jj"],
  resource
) when {
  true && (principal || action)
};
