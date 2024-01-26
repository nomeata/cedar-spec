forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && (resource == resource)) && true) && true
};
