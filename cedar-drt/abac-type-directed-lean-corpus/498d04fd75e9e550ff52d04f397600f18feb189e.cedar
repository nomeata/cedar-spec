permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && (action has "")) && (principal has "")) && true
};
