permit(
  principal is a in a::"\0\0\0\0\0\0\06",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[true, true, true], [true, false, false], [true, true, false]].containsAll([[false, true, false], [], []]))) && true) && true
};
