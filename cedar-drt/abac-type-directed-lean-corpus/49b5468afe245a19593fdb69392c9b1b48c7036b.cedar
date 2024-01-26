permit(
  principal == a::"\0~\0\0\0\0\0\0\0\0\0",
  action in [Action::"action",Action::"action"],
  resource == a::"\0~\0\0\0\0\0\0\0\0\0"
) when {
  ((true && ([[true, true, true], [true, false, true], [false, true]].containsAll([[true, true, true], [true, true, true], [true, false]]))) && true) && true
};
