permit(
  principal == a::"",
  action,
  resource == a::""
) when {
  ((true && ([].containsAll([[]]))) && (a::"" in principal)) && false
};
