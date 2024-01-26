permit(
  principal,
  action,
  resource == a::"jhjj"
) when {
  (true && principal) && action
};
