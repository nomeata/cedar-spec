permit(
  principal == a::"bXjjj",
  action == Action::"action",
  resource is a
) when {
  true && (((-(context)) in false) in principal)
};
