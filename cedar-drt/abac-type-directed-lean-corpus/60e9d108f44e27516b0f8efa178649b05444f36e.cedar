@B0h8Y("6")
permit(
  principal is a,
  action,
  resource is a in a::"+"
) when {
  true && (action has "")
};
