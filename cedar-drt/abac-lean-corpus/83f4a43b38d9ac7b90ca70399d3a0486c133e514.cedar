@AhhZh("")
forbid(
  principal,
  action,
  resource in a::""
) when {
  true && [resource, false]
};
