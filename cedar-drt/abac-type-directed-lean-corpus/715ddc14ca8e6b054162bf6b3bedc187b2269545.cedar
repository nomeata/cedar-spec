forbid(
  principal is a in a::"",
  action in [],
  resource is a in a::""
) when {
  (true && (((decimal("6")).lessThanOrEqual(decimal(""))) || (principal has ""))) && true
};
