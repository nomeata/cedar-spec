permit(
  principal in a::"",
  action,
  resource
) when {
  true && ((action[""]).containsAny(Action::"action".contains(a::"z" == "")))
};
