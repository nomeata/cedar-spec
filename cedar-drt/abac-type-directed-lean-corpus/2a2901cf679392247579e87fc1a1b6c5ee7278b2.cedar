permit(
  principal,
  action,
  resource in a::""
) when {
  ((true && (!([ip("0.23.105.0")].containsAny([ip("::36:285b:9333:d5d5")])))) && false) && false
};
