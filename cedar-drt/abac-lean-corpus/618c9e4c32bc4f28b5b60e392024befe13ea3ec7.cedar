forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::"i\0\0@"
) when {
  (true && (false.containsAny("j" && (action is a)))) && Action::"action"
};
