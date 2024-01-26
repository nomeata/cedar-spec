permit(
  principal == a::"",
  action == Action::"action",
  resource is a
) when {
  true && (((-(principal)) in principal) in principal)
};
