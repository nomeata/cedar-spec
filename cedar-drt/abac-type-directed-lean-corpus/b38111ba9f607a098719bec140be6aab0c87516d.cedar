permit(
  principal == a::"",
  action,
  resource is a in a::""
) when {
  true && (!((decimal("6\u{3}")).lessThan(decimal(""))))
};
