permit(
  principal == a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  ((true && ({"": false}[""])) && true) && true
};
