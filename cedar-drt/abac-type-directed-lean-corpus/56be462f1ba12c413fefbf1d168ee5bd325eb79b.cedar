forbid(
  principal is a in a::",A",
  action,
  resource == a::""
) when {
  true && ({"": false, "30": false} has "")
};
