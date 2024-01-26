@A("")
@q("")
@r("")
permit(
  principal,
  action,
  resource
) when {
  ((true && ((principal in principal)["A"])) && principal) && principal
};
