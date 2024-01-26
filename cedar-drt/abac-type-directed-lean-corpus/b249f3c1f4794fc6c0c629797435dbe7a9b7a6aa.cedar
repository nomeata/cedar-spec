permit(
  principal is a in a::"\0\0\06",
  action in [Action::"action"],
  resource
) when {
  ((true && ([[[], [], []], [[], [], []], [[], [], []]].containsAll([[true, true, true], [true, true, true], [false, true, false]]))) && true) && true
};
