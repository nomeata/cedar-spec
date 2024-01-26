permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ("" == "")) && true) && true
};
