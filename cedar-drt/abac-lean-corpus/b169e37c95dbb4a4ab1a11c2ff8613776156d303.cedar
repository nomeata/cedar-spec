permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a
) when {
  ((true && (!(!(if action then action else principal)))) && principal) && principal
};
