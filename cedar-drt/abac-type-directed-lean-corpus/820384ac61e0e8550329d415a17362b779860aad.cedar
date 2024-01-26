permit(
  principal,
  action in [Action::"action"],
  resource is a
) when {
  ((true && ((if (principal in principal) then true else true) == true)) && true) && true
};
