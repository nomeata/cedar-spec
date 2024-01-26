@B0h8Y("6")
permit(
  principal,
  action == Action::"action",
  resource is a in a::"\066"
) when {
  true && (principal has "")
};
