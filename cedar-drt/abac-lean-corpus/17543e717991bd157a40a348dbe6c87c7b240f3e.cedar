permit(
  principal == a::"",
  action,
  resource in a::""
) when {
  true && [false, action, principal, action]
};
