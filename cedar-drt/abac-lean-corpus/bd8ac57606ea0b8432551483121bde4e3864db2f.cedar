permit(
  principal,
  action,
  resource
) when {
  (true && a::"") && (!(principal == action))
};
