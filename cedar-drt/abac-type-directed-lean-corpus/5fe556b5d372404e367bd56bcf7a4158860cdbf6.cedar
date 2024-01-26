forbid(
  principal == a::"",
  action,
  resource
) when {
  (true && (!true)) && (!(principal in principal))
};
