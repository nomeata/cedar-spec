permit(
  principal == r::r::"\0\0",
  action,
  resource
) when {
  (true && r::Action::"action") && (!true)
};
