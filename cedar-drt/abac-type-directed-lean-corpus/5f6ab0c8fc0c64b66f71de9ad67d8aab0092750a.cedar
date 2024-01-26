permit(
  principal,
  action,
  resource
) when {
  ((true && ((if ((ip("5544..51.51.54/18")) == (ip("0.0.0.0"))) then (decimal("0.0")) else (decimal("0.0"))) == (decimal("0.0")))) && false) && false
};
