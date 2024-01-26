permit(
  principal == a::"bXjjj",
  action == Action::"action",
  resource is a
) when {
  true && (((-(action)) in Action::"action") in Action::"action")
};
