@A("")
permit(
  principal == a::"jjj\njj",
  action,
  resource
) when {
  true && (principal in principal)
};
