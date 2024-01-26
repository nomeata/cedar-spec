permit(
  principal is a,
  action == Action::"action",
  resource
) when {
  true && (action.lessThan(action, (false in principal) in principal, principal))
};
