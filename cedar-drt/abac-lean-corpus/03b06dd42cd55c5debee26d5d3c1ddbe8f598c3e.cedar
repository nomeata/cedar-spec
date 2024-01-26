forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && (r::")" in [false, principal])
};
