permit(
  principal,
  action,
  resource == a::"zj\0\0te"
) when {
  (true && (!principal)) && resource
};
