forbid(
  principal == a::"",
  action,
  resource is a in a::""
) when {
  false
};
