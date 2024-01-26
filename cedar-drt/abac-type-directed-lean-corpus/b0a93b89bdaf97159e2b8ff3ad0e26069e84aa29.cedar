forbid(
  principal == a::"",
  action,
  resource
) when {
  true && (resource has "r")
};
