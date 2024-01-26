permit(
  principal,
  action,
  resource is a
) when {
  (true && (action in [a::",", action, resource])) && true
};
