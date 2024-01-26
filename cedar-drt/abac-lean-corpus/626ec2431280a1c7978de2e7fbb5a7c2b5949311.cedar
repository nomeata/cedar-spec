forbid(
  principal == a::"",
  action,
  resource
) when {
  true && (r::")" in [false, principal])
};
