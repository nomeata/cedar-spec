permit(
  principal is a in a::"\0\0\0\0\0\0\0\06",
  action == Action::"action",
  resource
) when {
  ((true && ([[true, true, true], if true then [] else [], [false]].containsAll([[[], [], []], [[], []], []]))) && ((principal is a) == (Action::"action" in a::"\0\n\0\0\0\0\0\0\0"))) && true
};
