permit(
  principal is a in a::"=j",
  action,
  resource
) when {
  (true && (false in (context && action))) && action
};
