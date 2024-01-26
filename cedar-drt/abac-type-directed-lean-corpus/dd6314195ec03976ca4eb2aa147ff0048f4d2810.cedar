permit(
  principal,
  action,
  resource is a in a::","
) when {
  (true && (action in [a::",", a::",", a::""])) && true
};
