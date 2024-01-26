permit(
  principal == a::"bXjjj",
  action == Action::"action",
  resource is a
) when {
  true && (((-(context)) in a::"bXjjj") in context)
};
