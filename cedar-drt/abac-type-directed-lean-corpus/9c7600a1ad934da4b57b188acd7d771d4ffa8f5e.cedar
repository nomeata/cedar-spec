forbid(
  principal == a::"",
  action,
  resource is a in a::"\u{1a}"
) when {
  false
};
