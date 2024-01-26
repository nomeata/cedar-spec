permit(
  principal == a::"",
  action,
  resource
) when {
  true && (action has "on_constraintbj\0=")
};
