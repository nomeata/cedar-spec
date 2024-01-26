permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && ((ip("202.54.54.54/4")).isMulticast())) && false
};
