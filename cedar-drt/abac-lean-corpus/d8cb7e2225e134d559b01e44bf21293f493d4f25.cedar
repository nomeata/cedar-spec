permit(
  principal == a::"j",
  action == Action::"action",
  resource is a
) when {
  true && (((-(context)) in a::"j") in principal)
};
