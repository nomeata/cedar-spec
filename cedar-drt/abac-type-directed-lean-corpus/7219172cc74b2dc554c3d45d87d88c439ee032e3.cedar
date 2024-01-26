permit(
  principal is a in a::"6",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && ((action has "") == (action has ""))) && (action has "")) && true
};
