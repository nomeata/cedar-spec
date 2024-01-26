forbid(
  principal == a::"",
  action,
  resource
) when {
  (true && (!true)) && (!(action in principal))
};
