permit(
  principal,
  action == Action::"action",
  resource is a in a::"`666"
) when {
  true && (a::"`666" has "")
};
