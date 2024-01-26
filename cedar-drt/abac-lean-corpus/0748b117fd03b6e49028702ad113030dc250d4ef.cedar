forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ((a::"" * (-1)) * (-1))) && a::"") && a::""
};
