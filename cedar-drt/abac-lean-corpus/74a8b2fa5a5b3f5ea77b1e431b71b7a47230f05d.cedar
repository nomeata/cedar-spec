permit(
  principal == a::"",
  action,
  resource
) when {
  true && (true in action)
};
