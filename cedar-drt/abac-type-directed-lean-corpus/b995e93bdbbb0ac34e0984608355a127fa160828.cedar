permit(
  principal,
  action,
  resource == a::""
) when {
  ((true && (action is a)) && true) && false
};
