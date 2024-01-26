permit(
  principal == a::"",
  action,
  resource
) when {
  (true && ([resource in principal, action in resource].contains(!true))) && false
};
