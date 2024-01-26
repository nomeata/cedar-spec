permit(
  principal,
  action,
  resource == a::"7"
) when {
  ((true && (a::"7" is a)) && false) && false
};
