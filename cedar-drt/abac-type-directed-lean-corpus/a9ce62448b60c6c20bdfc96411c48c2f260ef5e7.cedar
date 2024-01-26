permit(
  principal in a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ((Action::"action" is a) == (Action::"action" is a))) && ((if (action is a) then Action::"action" else Action::"action") is a)) && (Action::"action" is a)
};
