permit(
  principal,
  action in [Action::"j;jj",Action::"",Action::"j"],
  resource
) when {
  true && (principal || action)
};
